import Langlands.GroupScheme.SimplyConnected.SplitPicardInputsStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypePointedMapStatement
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.DiagonalizableFppfQuotient
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.AbelianScheme.Kernel
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.GroupScheme.Reductive.PicardRootWeightLines
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.FiniteTorsionNormalizerScheme
import Langlands.GroupScheme.Torus.CentralDiagonalizableExtensionSplit
import Langlands.GroupScheme.Torus.AffineDiagonalizableGraph
import Langlands.CommutativeAlgebra.StronglyGradedInvertible
import Langlands.Algebra.RosenlichtTensorUnitsStatement
import Langlands.Algebra.RosenlichtTensorUnits
import Langlands.GroupScheme.Torus.UnitsProductAffineReduction
import Langlands.GroupScheme.Torus.UnitsProductGeometricReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypePointedMapReduction

/-! # Character lifting from a Picard-trivial split reductive target -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SplitPicardCharacterLifting

open Langlands.CommutativeAlgebra.StronglyGraded
open Langlands.AlgebraicGeometry.Picard

/-- Triviality of all line bundles transfers along an isomorphism of schemes. -/
theorem lineBundlesTrivial_of_isIso {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso g]
    (hY : ∀ L : LineBundle Y, Nonempty (L ≅ LineBundle.trivial Y))
    (L : LineBundle X) : Nonempty (L ≅ LineBundle.trivial X) := by
  obtain ⟨e⟩ := hY ((LineBundle.pullback g).obj L)
  exact ⟨LineBundle.isoOfPullbackIso g (e ≪≫ (LineBundle.pullbackTrivialIso g).symm)⟩

/-- In a strongly graded ring whose degree-zero spectrum has only trivial line
bundles, every degree contains a unit of the whole ring. -/
theorem exists_isUnit_mem_component {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    {c : A →+* AddMonoidAlgebra A M} (hs : IsStrong (c := c))
    (hPic : ∀ L : LineBundle (Spec (CommRingCat.of (degreeZero (c := c)))),
      Nonempty (L ≅ LineBundle.trivial _))
    (m : M) : ∃ u : A, IsUnit u ∧ u ∈ component (c := c) m := by
  have := invertible_component (c := c) (hs (-m))
  obtain ⟨e⟩ := Langlands.Algebra.nonempty_linearEquiv_of_lineBundlesTrivial_of_rankAtStalk_eq_one
    (R := CommRingCat.of (degreeZero (c := c))) hPic
    (ModuleCat.of (CommRingCat.of (degreeZero (c := c))) (component (c := c) m))
    (rankAtStalk_component (hs (-m)))
  exact ⟨_, isUnit_of_linearEquiv (hs (-m)) e, (e.symm 1).property⟩

/-- The multiplicative group as the diagonalizable group of `PUnit → ℤ`. -/
def gmIso (R : CommRingCat.{u}) :
    (Gm (Spec R)).toGrp ≅ (Diagonalizable.groupScheme R (PUnit.{u+1} → ℤ)).toGrp :=
  splitTorus.gmIso (Spec R) ≪≫
    (Diagonalizable.splitIso R (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm

/-- The homomorphism `PUnit → ℤ` to `N` sending the generator to `m`. -/
abbrev degreeHom {N : Type u} [AddCommGroup N] (m : N) : (PUnit.{u+1} → ℤ) →+ N :=
  (zmultiplesHom N m).comp (Pi.evalAddMonoidHom (fun _ : PUnit.{u+1} => ℤ) PUnit.unit)

/-- Every additive map out of `PUnit → ℤ` is determined by its generator. -/
theorem eq_degreeHom {N : Type u} [AddCommGroup N] (q : (PUnit.{u+1} → ℤ) →+ N) :
    q = degreeHom (q (fun _ => 1)) := by
  refine AddMonoidHom.ext fun n => ?_
  have hn : n = n PUnit.unit • (fun _ : PUnit.{u+1} => (1 : ℤ)) := by
    funext x
    cases x
    simp
  conv_lhs => rw [hn]
  rw [map_zsmul]
  rfl

/-- Maps out of a diagonalizable group scheme are determined on character points. -/
theorem diagonalizable_source_ext {R : CommRingCat.{u}} {N : Type u} [AddCommGroup N]
    {Y : Over (Spec R)} (a b : (Diagonalizable.groupScheme R N).X ⟶ Y)
    (h : ∀ (C : CommAlgCat.{u} R) (t : Multiplicative N →* Cˣ),
      CharacterAction.characterPoint t ≫ a = CharacterAction.characterPoint t ≫ b) :
    a = b := by
  let t₀ := Corepresented.affinePointsEquiv (Diagonalizable.functor R N)
    (Diagonalizable.grpCorepresentation R N) (Diagonalizable.algebra R N)
    (𝟙 ((algSpec R).obj (op (Diagonalizable.algebra R N))))
  have h₀ : CharacterAction.characterPoint t₀ =
      𝟙 ((algSpec R).obj (op (Diagonalizable.algebra R N))) :=
    MulEquiv.symm_apply_apply _ _
  have := h _ t₀
  rw [h₀] at this
  simpa only [Category.id_comp] using this

variable {k : Type u} [Field k]

/-- **Main construction.** Let `i` embed a diagonalizable group in a smooth connected
affine group `H`. A unit of the coordinate ring of `H` that is homogeneous of degree `m`
for translation by `i` yields, after Rosenlicht's theorem, a character of `H` whose
restriction along `i` is the character `m`. -/
theorem exists_hom_comp_eq_restrictMap
    (hR : MultiplicativeTypePointedMapStatement.{u})
    {N : Type u} [AddCommGroup N]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffine H.X.left]
    (hsm : Smooth H.X.hom) (hqc : QuasiCompact H.X.hom) (hcon : ConnectedSpace H.X.left)
    (i : (Diagonalizable.groupScheme (CommRingCat.of k) N).toGrp ⟶ H)
    (m : N) (u : AffineCoordinates.algebra H) (hu : IsUnit u)
    (hm : u ∈ component
      (c := (CharacterAction.coaction (CharacterAction.ofTranslation i)).hom.toRingHom) m) :
    ∃ ψ : H ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u+1} → ℤ)).toGrp,
      i ≫ ψ = Diagonalizable.restrictMap (CommRingCat.of k) (degreeHom m) := by
  classical
  let R := CommRingCat.of k
  let B := AffineCoordinates.algebra H
  let a := CharacterAction.ofTranslation i
  let D := Diagonalizable.groupScheme R (PUnit.{u+1} → ℤ)
  -- The identity coordinate point and the normalized unit.
  let e₀ : B ⟶ CommAlgCat.of R R :=
    (AffineCoordinates.pointEquiv H (CommAlgCat.of R R)).symm 1
  have hu₀ : e₀.hom u ≠ 0 := (hu.map e₀.hom).ne_zero
  let r : k := (e₀.hom u)⁻¹
  have hr : r ≠ 0 := inv_ne_zero hu₀
  let v : B := u * algebraMap k B r
  have hv₁ : e₀.hom v = 1 := by
    change e₀.hom (u * algebraMap k B r) = 1
    rw [map_mul, AlgHom.commutes]
    exact mul_inv_cancel₀ hu₀
  have hvunit : IsUnit v := hu.mul ((IsUnit.mk0 r hr).map (algebraMap k B))
  have hvm : v ∈ component
      (c := (CharacterAction.coaction a).hom.toRingHom) m := by
    have h0 : algebraMap k B r ∈ component
        (c := (CharacterAction.coaction a).hom.toRingHom) 0 :=
      CharacterAction.coaction_scalar a r
    simpa only [add_zero] using mul_mem_component hm h0
  -- The scheme map to `D(PUnit → ℤ)` given by the normalized unit.
  let tv : Multiplicative (PUnit.{u+1} → ℤ) →* Bˣ :=
    (zpowersHom Bˣ hvunit.unit).comp
      (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : PUnit.{u+1} => ℤ) PUnit.unit))
  let φ : H.X ⟶ D.X :=
    (AffineCoordinates.coordinateSchemeIso H).inv ≫ CharacterAction.characterPoint tv
  have hpt : ∀ {C : CommAlgCat.{u} R} (y : B ⟶ C),
      AffineCoordinates.pointEquiv H C y ≫ φ =
        CharacterAction.characterPoint (CharacterAction.mapCharacter y tv) := by
    intro C y
    rw [CharacterAction.characterPoint_mapCharacter]
    change ((algSpec R).map y.op ≫ (AffineCoordinates.coordinateSchemeIso H).hom) ≫
      (AffineCoordinates.coordinateSchemeIso H).inv ≫ CharacterAction.characterPoint tv = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  -- The map is pointed.
  let P := (algSpec R).obj (op (CommAlgCat.of R R))
  have hP : IsIso (toUnit P) := by
    have hleft : IsIso (toUnit P).left := by
      have h1 : (toUnit P).left = P.hom := by simp
      rw [h1]
      change IsIso (Spec.map (CommRingCat.ofHom (algebraMap R R)))
      rw [show CommRingCat.ofHom (algebraMap R R) = 𝟙 R from rfl, Spec.map_id]
      infer_instance
    have : IsIso ((Over.forget (Spec R)).map (toUnit P)) := hleft
    exact isIso_of_reflects_iso _ (Over.forget _)
  have hone : (1 : P ⟶ H.X) ≫ φ = 1 := by
    have h1 : (1 : P ⟶ H.X) = AffineCoordinates.pointEquiv H (CommAlgCat.of R R) e₀ :=
      (Equiv.apply_symm_apply _ _).symm
    rw [h1, hpt]
    have h2 : CharacterAction.mapCharacter e₀ tv = 1 := by
      have hu1 : Units.map e₀.hom.toRingHom.toMonoidHom hvunit.unit = 1 := by
        apply Units.ext
        exact hv₁
      apply MonoidHom.ext
      intro n
      change Units.map e₀.hom.toRingHom.toMonoidHom (hvunit.unit ^ (n.toAdd PUnit.unit)) = 1
      rw [map_zpow, hu1, one_zpow]
    rw [h2, CharacterAction.characterPoint_one]
  have hφ : η[H.X] ≫ φ = η[D.X] := by
    rw [← cancel_epi (toUnit P)]
    simpa only [Hom.one_def, Category.assoc] using hone
  -- Rosenlicht's theorem makes the map a homomorphism.
  have hmult : IsMultiplicativeType D.toGrp :=
    isMultiplicativeType_of_iso_diagonalizable (Iso.refl _)
  obtain ⟨ψ, hψ⟩ := hR k H D.toGrp hsm hqc hcon hmult φ hφ
  refine ⟨ψ, ?_⟩
  apply Grp.hom_ext
  apply diagonalizable_source_ext
  intro C t
  -- The identity point of `H` over `C`.
  let x₁ : B ⟶ C := e₀ ≫ CommAlgCat.ofHom (Algebra.ofId k C)
  have hx₁ : AffineCoordinates.pointEquiv H C x₁ = 1 := by
    rw [AffineCoordinates.pointEquiv_comp, Equiv.apply_symm_apply, MonObj.comp_one]
  have hix : CharacterAction.characterPoint t ≫ i.hom.hom =
      AffineCoordinates.pointEquiv H C (a.act t x₁) := by
    rw [CharacterAction.pointEquiv_ofTranslation_act, hx₁, mul_one]
  have hval : Units.map (a.act t x₁).hom.toRingHom.toMonoidHom hvunit.unit =
      t (Multiplicative.ofAdd m) := by
    apply Units.ext
    change (a.act t x₁).hom v = _
    rw [CharacterAction.act_eq_coaction_evaluate]
    change (CharacterAction.evaluate x₁ t).hom ((CharacterAction.coaction a).hom v) = _
    rw [show (CharacterAction.coaction a).hom v = AddMonoidAlgebra.single m v from hvm,
      CharacterAction.evaluate_single]
    change (Algebra.ofId k C) (e₀.hom v) * _ = _
    rw [hv₁, map_one, one_mul]
  have hchar : CharacterAction.mapCharacter (a.act t x₁) tv =
      t.comp (AddMonoidHom.toMultiplicative (degreeHom m)) := by
    apply MonoidHom.ext
    intro n
    change Units.map (a.act t x₁).hom.toRingHom.toMonoidHom
        (hvunit.unit ^ (n.toAdd PUnit.unit)) =
      t (Multiplicative.ofAdd ((n.toAdd PUnit.unit) • m))
    rw [map_zpow, hval, ofAdd_zsmul, map_zpow]
  change CharacterAction.characterPoint t ≫ i.hom.hom ≫ ψ.hom.hom =
    CharacterAction.characterPoint t ≫
      (Diagonalizable.restrictMap (CommRingCat.of k) (degreeHom m)).hom.hom
  rw [CharacterAction.characterPoint_restrictMap, hψ, ← Category.assoc, hix, hpt, hchar]

end SplitPicardCharacterLifting

open SplitPicardCharacterLifting in
/-- **Character lifting, conditional on Rosenlicht's theorem.** Given the pointed-map rigidity
statement for maps to diagonalizable groups, every character of the kernel of a central isogeny
`f : H ⟶ G` of split connected reductive groups lifts to `H` when every line bundle on `G` is
trivial. -/
theorem splitCentralIsogenyPicardCharacterLifting_of_pointedMap
    (hR : MultiplicativeTypePointedMapStatement.{u}) :
    SplitCentralIsogenyPicardCharacterLiftingStatement.{u} := by
  intro k _ H G hH hG hsH _ f hf hPic χ
  classical
  let R := CommRingCat.of k
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- The kernel is a closed subgroup of a split maximal torus, hence diagonalizable.
  obtain ⟨T, j, hT, hj⟩ := hsH
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hker : SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range j := by
    rw [← maximalTorusCentralizer k H hH T j hj]
    exact hf.kernel_range_le_center.trans (center_le_torusCentralizer j)
  let i₀ := hjrep.factorHom (kernelι f) hker
  have hi₀ : i₀ ≫ j = kernelι f := hjrep.factorHom_comp (kernelι f) hker
  have hι : IsClosedSubgroup (kernelι f) :=
    inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left)
  have hic : IsClosedSubgroup i₀ := IsClosedSubgroup.of_comp hj.2.1 (hi₀ ▸ hι)
  obtain ⟨N, _, _, ⟨e⟩⟩ := exists_diagonalizableIso_of_isClosedSubgroup_splitTorus hT i₀ hic
  -- The quotient of `H` by the diagonalizable kernel is `G`.
  let i' : (Diagonalizable.groupScheme R N).toGrp ⟶ H := e.inv ≫ kernelι f
  have hi' : IsClosedSubgroup i' := IsClosedSubgroup.iso_comp e.symm hι
  have hrange : SubgroupFunctor.range i' = SubgroupFunctor.range (kernelι f) :=
    SubgroupFunctor.range_iso_comp e.symm (kernelι f)
  have hn' : (SubgroupFunctor.range i').IsNormal :=
    (hf.isCentral_kernelι.comp e.inv).range_isNormal
  have hq := CharacterAction.quotientHom_isFppfQuotient i' hi' hn'
  have hf' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') f :=
    ⟨hf.flat, hf.surjective, hf.locallyOfFinitePresentation, hrange.symm⟩
  have : IsAffineHom (CharacterAction.quotientGroup i' hi' hn').X.hom :=
    CharacterAction.quotientGroup_isAffineHom i' hi' hn'
  have : IsAffine (CharacterAction.quotientGroup i' hi' hn').X.left :=
    isAffine_of_isAffineHom (CharacterAction.quotientGroup i' hi' hn').X.hom
  have : IsFinite f.hom.hom.left := hf.isFinite
  let φ := FppfQuotientComparison.iso hq hf'
  have : IsIso φ.inv.hom.hom := (Grp.forget (Over (Spec R))).map_isIso φ.inv
  have : IsIso φ.inv.hom.hom.left := (Over.forget (Spec R)).map_isIso φ.inv.hom.hom
  have hPic' := lineBundlesTrivial_of_isIso φ.inv.hom.hom.left hPic
  -- The character as an additive map of character groups.
  obtain ⟨q₀, hq₀⟩ := (DiagonalizableCharacter.restrictMap_bijective k N (PUnit.{u+1} → ℤ)).2
    (e.inv ≫ χ.toMul ≫ (gmIso R).hom)
  let m : N := q₀ (fun _ => 1)
  have hq₀m : q₀ = degreeHom m := eq_degreeHom q₀
  -- A unit of degree `m` and the resulting character of `H`.
  obtain ⟨v, hv, hvm⟩ := exists_isUnit_mem_component
    (CharacterAction.isStrong_ofTranslation i' hi') hPic' m
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_restrictMap hR H hH.smooth inferInstance
    hH.connectedSpace i' m v hv hvm
  refine ⟨Additive.ofMul (ψ ≫ (gmIso R).inv), ?_⟩
  have hk : kernelι f = e.hom ≫ i' := by
    change kernelι f = e.hom ≫ e.inv ≫ kernelι f
    rw [Iso.hom_inv_id_assoc]
  have key : kernelι f ≫ ψ ≫ (gmIso R).inv = χ.toMul := by
    have hq₀' : Diagonalizable.restrictMap (CommRingCat.of k) q₀ =
        e.inv ≫ χ.toMul ≫ (gmIso R).hom := hq₀
    rw [hk, Category.assoc, reassoc_of% hψ, ← hq₀m, hq₀']
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact (congrArg Additive.ofMul key).trans (ofMul_toMul χ)

/-- Rosenlicht's tensor-unit statement gives pointed-map rigidity for maps to groups of
multiplicative type, through the published affine and geometric reductions. -/
theorem multiplicativeTypePointedMap_of_rosenlichtTensorUnits
    (hT : Langlands.Algebra.RosenlichtTensorUnitsStatement.{u, u, u}) :
    MultiplicativeTypePointedMapStatement.{u} :=
  multiplicativeTypePointedMap_of_unitsProductDecomposition
    (UnitsProduct.geometric_reduction
      (fun k _ _ X Y _ _ _ _ _ _ f =>
        UnitsProduct.affine_splitting_of_domain_tensor_units
          (fun k _ _ A _ _ _ _ B _ _ _ _ => hT k A B) k X Y f))

/-- **Character lifting, conditional on Rosenlicht's tensor-unit statement.** -/
theorem splitCentralIsogenyPicardCharacterLifting_of_rosenlichtTensorUnits
    (hT : Langlands.Algebra.RosenlichtTensorUnitsStatement.{u, u, u}) :
    SplitCentralIsogenyPicardCharacterLiftingStatement.{u} :=
  splitCentralIsogenyPicardCharacterLifting_of_pointedMap
    (multiplicativeTypePointedMap_of_rosenlichtTensorUnits hT)

/-- **Character lifting from a Picard-trivial split reductive target.** For a central isogeny
`f : H ⟶ G` of connected reductive groups over a field, each with a split maximal torus, if every
line bundle on `G` is trivial then every character of the full kernel of `f` extends to `H`. -/
theorem splitCentralIsogenyPicardCharacterLifting :
    SplitCentralIsogenyPicardCharacterLiftingStatement.{u} :=
  splitCentralIsogenyPicardCharacterLifting_of_rosenlichtTensorUnits
    Langlands.Algebra.rosenlichtTensorUnits.{u, u, u}

end Langlands.GroupScheme
