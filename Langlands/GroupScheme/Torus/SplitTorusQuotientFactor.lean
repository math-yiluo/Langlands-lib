import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Reductive.Basic

/-! # Homomorphisms into split tori factor through split-torus fppf quotients

Let `H` be a smooth connected affine group over a field `k` and `f : H ⟶ T` a homomorphism into a
split torus. Choosing coordinates `T ≅ 𝔾_m^I`, the coordinate characters `cᵢ` of `f` span a
lattice `L` of rational characters of `H`. Evaluation of the characters in `L` is a homomorphism
`q : H ⟶ D(L)` to the diagonalizable group of `L`, and restriction of characters along
`ℤ^I ↠ L` is a closed immersion `m : D(L) ⟶ T` with `q ≫ m = f`.

Since `H` is integral, `L` is a free `ℤ`-module of finite rank, so `D(L)` is a split torus. The
classifying algebra map `k[L] → O(H)` of `q` sends `l` to the unit of `O(H)` attached to `l`; these
units are linearly independent, so the algebra map is injective, `q` is dominant, and `D(L)` is
integral. Hence `q` is flat and surjective (`DominantHomFlat`), of finite presentation, and its
kernel is the kernel of `f` because `m` is a monomorphism.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitTorusQuotientFactor

/-! ### The lattice spanned by finitely many characters -/

section Lattice

variable {S : Scheme.{u}} {H : GroupScheme S} {I : Type u} [Fintype I]

/-- The additive map `n ↦ ∑ nᵢ cᵢ` from `ℤ^I` to the rational characters of `H`. -/
def latticeHom (c : I → rationalCharacters H) : (I → ℤ) →+ rationalCharacters H where
  toFun n := ∑ i, n i • c i
  map_zero' := by simp
  map_add' n n' := by simp [add_smul, Finset.sum_add_distrib]

theorem latticeHom_single [DecidableEq I] (c : I → rationalCharacters H) (i : I) :
    latticeHom c (Pi.single i 1) = c i := by
  simp [latticeHom, Pi.single_apply]

end Lattice

variable {k : Type u} [Field k]

local notation "R" => CommRingCat.of k

/-! ### The quotient homomorphism to a diagonalizable group -/

section Quotient

variable {H : GroupScheme (Spec (CommRingCat.of k))} (L : AddSubgroup (rationalCharacters H))

/-- The values at a point of the characters in `L`, as a character of `L`. -/
def charPoint (T : Over (Spec R)) (x : T ⟶ H.X) : Multiplicative L →* (Γ(T.left, ⊤))ˣ where
  toFun l := characterEval (Multiplicative.toAdd l : L).1 T x
  map_one' := characterEval_zero T x
  map_mul' _ _ := characterEval_add _ _ T x

theorem charPoint_apply (T : Over (Spec R)) (x : T ⟶ H.X) (l : Multiplicative L) :
    charPoint L T x l = characterEval (Multiplicative.toAdd l : L).1 T x :=
  rfl

/-- Evaluation of the characters in `L` is multiplicative in the point. -/
def charPointHom (T : Over (Spec R)) :
    (T ⟶ H.X) →* (Diagonalizable.functor R L).obj ((algΓ R).obj T).unop where
  toFun x := charPoint L T x
  map_one' := by
    apply MonoidHom.ext
    intro l
    exact map_one (characterEval (Multiplicative.toAdd l : L).1 T)
  map_mul' x y := by
    apply MonoidHom.ext
    intro l
    exact map_mul (characterEval (Multiplicative.toAdd l : L).1 T) x y

/-- The points of the quotient map `H ⟶ D(L)`. -/
def quotientPoints (T : Over (Spec R)) :
    (T ⟶ H.X) →* (T ⟶ (Diagonalizable.groupScheme R L).toGrp.X) :=
  (Corepresented.pointsEquiv (Diagonalizable.functor R L)
    (Diagonalizable.grpCorepresentation R L) T).symm.toMonoidHom.comp (charPointHom L T)

theorem quotientPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ H.X) :
    quotientPoints L T' (a ≫ x) = a ≫ quotientPoints L T x := by
  have h₁ : ∀ (T : Over (Spec R)) (y : T ⟶ H.X), Corepresented.pointsEquiv
      (Diagonalizable.functor R L) (Diagonalizable.grpCorepresentation R L) T
        (quotientPoints L T y) = charPointHom L T y :=
    fun T y => MulEquiv.apply_symm_apply _ _
  have h₂ : Corepresented.pointsEquiv (Diagonalizable.functor R L)
      (Diagonalizable.grpCorepresentation R L) T' (a ≫ quotientPoints L T x) =
        (Diagonalizable.functor R L).map ((algΓ R).map a).unop (charPointHom L T x) := by
    rw [← h₁]
    exact Corepresented.pointsEquiv_naturality (Diagonalizable.functor R L)
      (Diagonalizable.grpCorepresentation R L) a (quotientPoints L T x)
  apply (Corepresented.pointsEquiv (Diagonalizable.functor R L)
    (Diagonalizable.grpCorepresentation R L) T').injective
  rw [h₁]
  erw [h₂]
  apply MonoidHom.ext
  intro l
  apply Units.ext
  change (characterEval (Multiplicative.toAdd l : L).1 T' (a ≫ x) : Γ(T'.left, ⊤)) =
    ((algΓ R).map a).unop.hom (characterEval (Multiplicative.toAdd l : L).1 T x : Γ(T.left, ⊤))
  rw [characterEval_naturality]
  rfl

/-- The quotient homomorphism `H ⟶ D(L)`, evaluating the characters in `L`. -/
def quotientHom : H ⟶ (Diagonalizable.groupScheme R L).toGrp :=
  homOfPoints (quotientPoints L) (quotientPoints_naturality L)

theorem pointsEquiv_quotientHom (T : Over (Spec R)) (x : T ⟶ H.X) :
    Corepresented.pointsEquiv (Diagonalizable.functor R L) (Diagonalizable.grpCorepresentation R L)
      T (x ≫ (quotientHom L).hom.hom) = charPoint L T x := by
  rw [quotientHom]
  erw [comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

end Quotient

/-! ### The closed immersion into the split torus -/

section Inclusion

variable {H : GroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Fintype I]
  (c : I → rationalCharacters H)

/-- The closed immersion `D(L) ⟶ D(ℤ^I)` restricting characters along `ℤ^I ↠ L`. -/
def inclusionHom :
    (Diagonalizable.groupScheme R (latticeHom c).range).toGrp ⟶
      (Diagonalizable.groupScheme R (I → ℤ)).toGrp :=
  Corepresented.groupSchemeMap (Diagonalizable.grpCorepresentation R (latticeHom c).range)
    (Diagonalizable.grpCorepresentation R (I → ℤ))
    (Diagonalizable.restrict R (latticeHom c).rangeRestrict)

theorem inclusionHom_hom_left :
    (inclusionHom c).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (Diagonalizable.incl R (latticeHom c).rangeRestrict).hom.toRingHom) := by
  rw [inclusionHom, Corepresented.groupSchemeMap_hom_left]
  simp only [Corepresented.classify]
  erw [Diagonalizable.homEquiv_symm_restrict]
  erw [Equiv.symm_apply_apply, Category.comp_id]

theorem isClosedImmersion_inclusionHom : IsClosedImmersion (inclusionHom c).hom.hom.left := by
  rw [inclusionHom_hom_left]
  exact IsClosedImmersion.spec_of_surjective _
    (Diagonalizable.incl_surjective _ (latticeHom c).rangeRestrict_surjective)

end Inclusion

/-! ### The factorization -/

section Factor

variable {H G : GroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Fintype I] [DecidableEq I]
  (e : G ≅ splitTorus (Spec (CommRingCat.of k)) I) (f : H ⟶ G)

/-- The coordinate characters of `f` in the split coordinates `e`. -/
def coordChar (i : I) : rationalCharacters H :=
  characterRestrict (f ≫ e.hom) (Additive.ofMul (Limits.Pi.π (fun _ : I => (Gm (Spec R)).toGrp) i))

omit [DecidableEq I] in
theorem characterEval_coordChar (i : I) (T : Over (Spec R)) (x : T ⟶ H.X) :
    characterEval (coordChar e f i) T x =
      splitTorus.pointsEquiv I T (x ≫ (f ≫ e.hom).hom.hom) i := by
  rw [coordChar, characterEval_characterRestrict, characterEval_apply,
    splitTorus.pointsEquiv_apply]
  rfl

theorem quotientHom_inclusionHom_splitIso :
    quotientHom (latticeHom (coordChar e f)).range ≫ inclusionHom (coordChar e f) ≫
        (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).hom = f ≫ e.hom := by
  apply hom_ext_points
  intro T x
  apply (splitTorus.pointsEquiv I T).injective
  change splitTorus.pointsEquiv I T
      (((x ≫ (quotientHom (latticeHom (coordChar e f)).range).hom.hom) ≫
        (inclusionHom (coordChar e f)).hom.hom) ≫
          (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).hom.hom.hom) =
    splitTorus.pointsEquiv I T (x ≫ (f ≫ e.hom).hom.hom)
  rw [splitTorus.diagonalizable_splitIso_points]
  funext i
  rw [← characterEval_coordChar]
  change DFunLike.coe (F := Multiplicative (I → ℤ) →* (((algΓ R).obj T).unop)ˣ)
      (Corepresented.pointsEquiv (Diagonalizable.functor R (I → ℤ))
        (Diagonalizable.grpCorepresentation R (I → ℤ)) T
        ((x ≫ (quotientHom (latticeHom (coordChar e f)).range).hom.hom) ≫
          (inclusionHom (coordChar e f)).hom.hom))
      (Multiplicative.ofAdd (Pi.single i 1)) = _
  rw [inclusionHom]
  erw [Corepresented.groupSchemeMap_points, Diagonalizable.restrict_app_apply,
    pointsEquiv_quotientHom]
  change characterEval (latticeHom (coordChar e f) (Pi.single i 1)) T x = _
  rw [latticeHom_single]

end Factor

/-! ### Kernels along a monomorphism -/

section Kernel

variable {S : Scheme.{u}} {H D G : GroupScheme S}

/-- Composing with a homomorphism that is a monomorphism of schemes does not change the kernel. -/
theorem range_kernelι_comp (q : H ⟶ D) (m : D ⟶ G) [Mono m.hom.hom.left] :
    SubgroupFunctor.range (kernelι (q ≫ m)) = SubgroupFunctor.range (kernelι q) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  change x ≫ q.hom.hom ≫ m.hom.hom = 1 ↔ _
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply (cancel_mono m.hom.hom.left).mp
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, h, MonObj.one_comp]
  · intro h
    rw [← Category.assoc, h, MonObj.one_comp]

end Kernel

/-! ### Geometry of the quotient map -/

section Geometry

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  (L : AddSubgroup (rationalCharacters H))

/-- The units of `O(H)` attached to the characters in `L`. -/
def unitChar : Multiplicative L →* (CharacterUnits.Coord H)ˣ where
  toFun l := CharacterUnits.unit (Multiplicative.toAdd l : L).1
  map_one' := CharacterUnits.unit_zero
  map_mul' _ _ := CharacterUnits.unit_add _ _

/-- The algebra map `k[L] → O(H)` sending `l` to the unit of `O(H)` attached to `l`. -/
abbrev coordMap : Diagonalizable.algebra R L ⟶ CharacterUnits.Coord H :=
  Diagonalizable.lift R L (unitChar L)

theorem coordMap_apply (a : AddMonoidAlgebra R L) :
    (coordMap L).hom a = Finsupp.linearCombination R
      (fun l : L => (CharacterUnits.unit l.1 : CharacterUnits.Coord H)) a.coeff := by
  rw [Finsupp.linearCombination_apply]
  exact AddMonoidAlgebra.lift_apply _ a

theorem coordMap_injective : Function.Injective (coordMap L).hom := by
  have hli : LinearIndependent R
      (fun l : L => (CharacterUnits.unit l.1 : CharacterUnits.Coord H)) :=
    (CharacterUnits.linearIndependent_unit (G := H)).comp _ Subtype.val_injective
  intro a b hab
  rw [coordMap_apply, coordMap_apply] at hab
  exact AddMonoidAlgebra.coeff_injective
    ((show Function.Injective (Finsupp.linearCombination R
      (fun l : L => (CharacterUnits.unit l.1 : CharacterUnits.Coord H))) from hli) hab)

theorem functor_map_charPoint :
    (Diagonalizable.functor R L).map
        (Corepresented.affineSectionsIso (CharacterUnits.Coord H)).hom
        (charPoint L ((algSpec R).obj (op (CharacterUnits.Coord H)))
          (Lie.coordinateIso H).hom) = unitChar L := by
  apply MonoidHom.ext
  intro l
  apply Units.ext
  change (Corepresented.affineSectionsIso (CharacterUnits.Coord H)).hom.hom.toRingHom
      (characterEval (Multiplicative.toAdd l : L).1 _ (Lie.coordinateIso H).hom :
        Γ(((algSpec R).obj (op (CharacterUnits.Coord H))).left, ⊤)) =
    (CharacterUnits.unit (Multiplicative.toAdd l : L).1 : CharacterUnits.Coord H)
  rw [Corepresented.affineSectionsIso_hom_ringHom, CharacterUnits.unit,
    CharacterUnits.universalPoint_eq]
  rfl

/-- At the coordinate presentation of `H`, the quotient map is the spectrum of `coordMap`. -/
theorem coordinateIso_comp_quotientHom :
    (Lie.coordinateIso H).hom ≫ (quotientHom L).hom.hom = (algSpec R).map (coordMap L).op := by
  have hx := Corepresented.map_affineSectionsIso_pointsEquiv (Diagonalizable.functor R L)
    (Diagonalizable.grpCorepresentation R L) (CharacterUnits.Coord H)
    ((Lie.coordinateIso H).hom ≫ (quotientHom L).hom.hom)
  erw [pointsEquiv_quotientHom, functor_map_charPoint, Corepresented.affinePointsEquiv_apply] at hx
  have hpre : (algSpec.fullyFaithful.preimage
      ((Lie.coordinateIso H).hom ≫ (quotientHom L).hom.hom)).unop = coordMap L := by
    apply (Diagonalizable.grpCorepresentation R L).homEquiv.injective
    refine hx.symm.trans ?_
    exact ((Diagonalizable.corepresentation R L).homEquiv.apply_symm_apply (unitChar L)).symm
  rw [← hpre]
  exact (algSpec.fullyFaithful.map_preimage _).symm

theorem isDominant_spec_map_of_injective {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (h : Function.Injective φ) : IsDominant (Spec.map φ) := by
  constructor
  change DenseRange (PrimeSpectrum.comap φ.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp h]
  exact bot_le

theorem isDominant_quotientHom : IsDominant (quotientHom L).hom.hom.left := by
  have : IsDominant ((Lie.coordinateIso H).hom.left ≫ (quotientHom L).hom.hom.left) := by
    rw [← Over.comp_left, coordinateIso_comp_quotientHom, algSpec_map_left]
    exact isDominant_spec_map_of_injective _ (coordMap_injective L)
  exact IsDominant.of_comp (Lie.coordinateIso H).hom.left _

theorem isDomain_algebra [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    IsDomain (AddMonoidAlgebra R L) := by
  have := CharacterLatticeProof.isDomain_coord H
  exact Function.Injective.isDomain (coordMap L).hom (coordMap_injective L)

theorem isIntegral_quotient [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    IsIntegral (Diagonalizable.groupScheme R L).toGrp.X.left := by
  have := isDomain_algebra L
  change IsIntegral (Spec (CommRingCat.of (AddMonoidAlgebra R L)))
  infer_instance

/-- The character lattice `L` of a smooth connected affine group is free of finite rank. -/
theorem free_finite [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    Module.Free ℤ L ∧ Module.Finite ℤ L := by
  classical
  have := CharacterLatticeProof.isDomain_coord H
  let K : Type u := CommRingCat.of k
  let _ : Field K := inferInstanceAs (Field k)
  set D := CharacterUnits.Coord H
  set F := FractionRing D
  let w : Multiplicative L →* F :=
    { toFun := fun l => algebraMap D F (CharacterUnits.unit (Multiplicative.toAdd l : L).1 : D)
      map_one' := by simp [CharacterUnits.unit_zero]
      map_mul' := fun a b => by simp [toAdd_mul, CharacterUnits.unit_add] }
  have hw : LinearIndependent K (CharacterLattice.wa w) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom K D F) :=
      IsFractionRing.injective D F
    exact ((CharacterUnits.linearIndependent_unit (G := H)).comp _ Subtype.val_injective).map'
      (IsScalarTower.toAlgHom K D F).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨s, hs⟩ := (Lie.coordinateAlgebraFiniteType H).out
  refine CharacterLattice.free_and_finite (k := K) w hw (s.image (algebraMap D F)) fun l => ?_
  change algebraMap D F (CharacterUnits.unit l.1 : D) ∈ _
  rw [Finset.coe_image, ← IsScalarTower.coe_toAlgHom' K D F, Algebra.adjoin_image]
  exact Subalgebra.mem_map.mpr ⟨_, hs ▸ Algebra.mem_top, rfl⟩

/-- The quotient map is an fppf cover: flat, surjective and locally of finite presentation. -/
theorem quotientHom_fppf [Smooth H.X.hom] [ConnectedSpace H.X.left] :
    Flat (quotientHom L).hom.hom.left ∧ Surjective (quotientHom L).hom.hom.left ∧
      LocallyOfFinitePresentation (quotientHom L).hom.hom.left := by
  set D := (Diagonalizable.groupScheme R L).toGrp
  set q := (quotientHom L).hom.hom
  have := isIntegral_quotient L
  have := isDominant_quotientHom L
  have hfree := free_finite L
  have hsplit : IsSplitTorus D := by
    classical
    obtain ⟨_, _⟩ := hfree
    exact Diagonalizable.isSplitTorus R (Module.Free.chooseBasis ℤ L).equivFun.toAddEquiv
  have := hsplit.smooth
  have : IsLocallyNoetherian D.X.left := LocallyOfFiniteType.isLocallyNoetherian D.X.hom
  have : LocallyOfFiniteType (q.left ≫ D.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left D.X.hom
  have : QuasiCompact (q.left ≫ D.X.hom) := by
    rw [Over.w]
    infer_instance
  have : QuasiCompact q.left := QuasiCompact.of_comp q.left D.X.hom
  have : Flat q.left := DominantHomFlat.flat_of_isDominant (quotientHom L)
  exact ⟨this, DominantHomFlat.surjective_of_flat (quotientHom L), inferInstance⟩

end Geometry

end SplitTorusQuotientFactor

open SplitTorusQuotientFactor in
/-- A homomorphism `f : H ⟶ T` from a smooth connected affine group over a field into a split
torus factors as an fppf quotient map `q : H ⟶ D` onto a split torus, with kernel the kernel of
`f`, followed by a closed immersion `m : D ⟶ T`. -/
theorem IsSplitTorus.exists_fppfQuotient_factor {k : Type u} [Field k]
    {H T : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left] (hT : IsSplitTorus T) (f : H ⟶ T) :
    ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ D) (m : D ⟶ T),
      IsSplitTorus D ∧ IsClosedSubgroup m ∧ q ≫ m = f ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have : Fintype I := Fintype.ofFinite I
  set L := (latticeHom (coordChar e f)).range
  set m := inclusionHom (coordChar e f) ≫
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).hom ≫ e.inv
  have hm : IsClosedImmersion m.hom.hom.left := by
    have := isClosedImmersion_inclusionHom (coordChar e f)
    have : IsIso (Diagonalizable.splitIso (CommRingCat.of k)
        (AddEquiv.refl (I → ℤ))).hom.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map
        (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).hom))
    have : IsIso e.inv.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map e.inv))
    change IsClosedImmersion ((inclusionHom (coordChar e f)).hom.hom.left ≫
      (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).hom.hom.hom.left ≫
        e.inv.hom.hom.left)
    infer_instance
  have hfac : quotientHom L ≫ m = f := by
    have h := quotientHom_inclusionHom_splitIso e f
    calc quotientHom L ≫ m = (quotientHom L ≫ inclusionHom (coordChar e f) ≫
          (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).hom) ≫ e.inv := by
          simp only [m, Category.assoc]
      _ = f := by rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨hflat, hsurj, hlfp⟩ := quotientHom_fppf L
  refine ⟨(Diagonalizable.groupScheme (CommRingCat.of k) L).toGrp, quotientHom L, m, ?_, hm, hfac,
    hflat, hsurj, hlfp, ?_⟩
  · obtain ⟨_, _⟩ := free_finite L
    exact Diagonalizable.isSplitTorus _ (Module.Free.chooseBasis ℤ L).equivFun.toAddEquiv
  · rw [← hfac, range_kernelι_comp]

end Langlands.GroupScheme
