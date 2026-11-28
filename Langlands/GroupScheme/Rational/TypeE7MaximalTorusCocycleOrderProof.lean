import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE7Inputs
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple
import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Reductive.StarActionFiniteStageLift
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessityIndependentProof
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof
import Langlands.GroupScheme.Torus.InducedPermutationBasis
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof
import Langlands.GroupScheme.Torus.WeilRestrictionSemilocalCocycle
import Langlands.LinearAlgebra.E7Casimir

/-! # Torus cocycles of simply connected groups of type `E₇` have order dividing `36` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TypeE7MaximalTorusCocycleOrder

/-! ### The permutation lattice of the roots -/

section RootLattice

variable {Γ ι M N : Type*} [Monoid Γ] [AddCommGroup M] [AddCommGroup N]
  (P : RootDatum ι M N) (act : Γ →* P.Aut)

/-- The permutation representation on `ℤ[Φ] = ι →₀ ℤ` of a monoid acting on a root datum. -/
def rootRep : Representation ℤ Γ (ι →₀ ℤ) where
  toFun γ := Finsupp.lmapDomain ℤ ℤ ((RootPairing.Equiv.indexHom P).comp act γ)
  map_one' := by
    rw [map_one, Equiv.Perm.coe_one, Finsupp.lmapDomain_id]
    rfl
  map_mul' γ δ := by
    rw [map_mul, Equiv.Perm.coe_mul, Finsupp.lmapDomain_comp]
    rfl

variable {P act}

theorem rootRep_single (γ : Γ) (i : ι) (n : ℤ) :
    rootRep P act γ (Finsupp.single i n) = Finsupp.single ((act γ).indexEquiv i) n := by
  simp [rootRep, Finsupp.mapDomain_single]

variable (P)

/-- The map `ℤ[Φ] → X`, `[α] ↦ α`. -/
def rootCombination : (ι →₀ ℤ) →ₗ[ℤ] M := Finsupp.linearCombination ℤ fun i => P.root i

/-- The map `X → ℤ[Φ]`, `x ↦ ∑_α ⟨x, α^∨⟩ [α]`. -/
def corootCoefficients [Fintype ι] : M →ₗ[ℤ] (ι →₀ ℤ) :=
  ∑ i, Finsupp.lsingle i ∘ₗ P.toLinearMap.flip (P.coroot i)

variable {P}

theorem rootCombination_single (i : ι) (n : ℤ) :
    rootCombination P (Finsupp.single i n) = n • P.root i := by
  simp [rootCombination]

theorem corootCoefficients_apply [Fintype ι] (x : M) :
    corootCoefficients P x = ∑ i, Finsupp.single i (P.toLinearMap x (P.coroot i)) := by
  simp [corootCoefficients]

theorem rootCombination_corootCoefficients [Fintype ι] (x : M) :
    rootCombination P (corootCoefficients P x) =
      ∑ i, P.toLinearMap x (P.coroot i) • P.root i := by
  simp [corootCoefficients_apply, map_sum, rootCombination_single]

theorem rootCombination_rootRep (γ : Γ) (m : ι →₀ ℤ) :
    rootCombination P (rootRep P act γ m) = (act γ).weightMap (rootCombination P m) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => simp only [map_add, hm, hm']
  | single i n =>
    rw [rootRep_single, rootCombination_single, rootCombination_single, map_zsmul,
      RootPairing.Hom.root_weightMap_apply]

theorem corootCoefficients_weightMap [Fintype ι] (γ : Γ) (x : M) :
    corootCoefficients P ((act γ).weightMap x) = rootRep P act γ (corootCoefficients P x) := by
  rw [corootCoefficients_apply, corootCoefficients_apply, map_sum,
    ← (act γ).indexEquiv.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rootRep_single, E7Casimir.toLinearMap_weightMap_coroot_indexEquiv]

end RootLattice

/-! ### Galois pinning data with a prescribed torus -/

section PinningData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

theorem pinningDataOfSplittingField_torus (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (E : Type u) [Field E] [Algebra k E]
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp) :
    (GaloisPinningData.ofSplittingField hG T i hi E hsplit).torus = T :=
  rfl

end PinningData

/-! ### An induced torus through which `n • 𝟙 T` factors -/

section Factorization

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- If the roots of Galois pinning data satisfy `∑_α ⟨x, α^∨⟩ α = n x` for all characters `x`,
then `n • 𝟙 T` factors through an induced torus, `T` being the torus of the data. -/
theorem exists_inducedTorus_comp_eq_zsmul (d : GaloisPinningData k E G)
    [Fintype d.toSplitPinning.rootIndex]
    (n : ℤ)
    (h : ∀ x, ∑ i, d.toSplitPinning.rootDatum.toLinearMap x
      (d.toSplitPinning.rootDatum.coroot i) • d.toSplitPinning.rootDatum.root i = n • x) :
    ∃ (Q : CommGroupScheme (Spec (CommRingCat.of k))) (f : d.torus ⟶ Q) (g : Q ⟶ d.torus),
      IsInducedTorus Q ∧ f ≫ g = n • 𝟙 d.torus := by
  classical
  let P := d.toSplitPinning.rootDatum
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  let ρ := rootRep P d.galoisAction
  obtain ⟨Q, eQ, hQsplit, hQeq⟩ :=
    torusGaloisLatticeRealization k E (d.toSplitPinning.rootIndex →₀ ℤ) ρ
  have hQ : IsInducedTorus Q :=
    isInducedTorus_of_equivariant_basis Q E hQsplit ρ Finsupp.basisSingleOne
      eQ.toIntLinearEquiv (fun σ x => hQeq σ x) (fun σ i =>
        ⟨(d.galoisAction σ).indexEquiv i, by
          exact rootRep_single σ i 1⟩)
  have hgal : ∀ (σ : E ≃ₐ[k] E) (x : characterLattice (bc.obj d.torus)),
      (d.galoisAction σ).weightMap x = characterLattice.galoisRepresentation k E d.torus σ x :=
    fun σ x => StarActionIndependence.galoisAction_weightMap_apply d σ x
  -- The pullback of characters along `f : T → Q`.
  let F₁ : characterLattice (bc.obj Q) →+ characterLattice (bc.obj d.torus) :=
    (rootCombination P).toAddMonoidHom.comp eQ.symm.toAddMonoidHom
  have hF₁ : ∀ (σ : E ≃ₐ[k] E) (χ : characterLattice (bc.obj Q)),
      F₁ (characterLattice.galoisRepresentation k E Q σ χ) =
        characterLattice.galoisRepresentation k E d.torus σ (F₁ χ) := by
    intro σ χ
    have hχ : eQ.symm (characterLattice.galoisRepresentation k E Q σ χ) = ρ σ (eQ.symm χ) := by
      rw [AddEquiv.symm_apply_eq, hQeq, AddEquiv.apply_symm_apply]
    change rootCombination P (eQ.symm _) = _
    rw [hχ, rootCombination_rootRep, hgal]
    rfl
  -- The pullback of characters along `g : Q → T`.
  let F₂ : characterLattice (bc.obj d.torus) →+ characterLattice (bc.obj Q) :=
    eQ.toAddMonoidHom.comp (corootCoefficients P).toAddMonoidHom
  have hF₂ : ∀ (σ : E ≃ₐ[k] E) (x : characterLattice (bc.obj d.torus)),
      F₂ (characterLattice.galoisRepresentation k E d.torus σ x) =
        characterLattice.galoisRepresentation k E Q σ (F₂ x) := by
    intro σ x
    change eQ (corootCoefficients P _) =
      characterLattice.galoisRepresentation k E Q σ (eQ (corootCoefficients P x))
    rw [← hgal, corootCoefficients_weightMap, hQeq]
  obtain ⟨f, hf, -⟩ := hQsplit.existsUnique_hom_of_equivariant_characterMap (T := d.torus) F₁ hF₁
  obtain ⟨g, hg, -⟩ := d.isSplitTorus.existsUnique_hom_of_equivariant_characterMap (T := Q) F₂ hF₂
  refine ⟨Q, f, g, hQ, ?_⟩
  obtain ⟨a, -, huniq⟩ := d.isSplitTorus.existsUnique_hom_of_equivariant_characterMap
    (T := d.torus) (n • AddMonoidHom.id _) (fun σ χ => by simp)
  have h1 : f ≫ g = a := huniq (f ≫ g) (fun χ => by
    rw [Functor.map_comp, Category.assoc, hg, hf]
    change rootCombination P (eQ.symm (eQ (corootCoefficients P χ))) = _
    rw [AddEquiv.symm_apply_apply, rootCombination_corootCoefficients, h]
    rfl)
  have h2 : n • 𝟙 d.torus = a := huniq (n • 𝟙 d.torus) (fun χ => by
    rw [TorusSurjectionIsogenySection.baseChange_map_zsmul_id, Preadditive.zsmul_comp,
      Category.id_comp]
    rfl)
  rw [h1, h2]

end Factorization

/-! ### Cocycles of induced tori -/

/-- Every cocycle of an induced torus over `K` on a field cover `Spec L → Spec K` is trivial. -/
theorem isTrivial_of_isInducedTorus (K L : Type u) [Field K] [Field L] [Algebra K L]
    (Q : CommGroupScheme (Spec (CommRingCat.of K))) (hQ : IsInducedTorus Q)
    (ξ : Cocycle Q.toGrp (GaloisCocycle.cover K L)) : ξ.IsTrivial := by
  have hp := hQ
  obtain ⟨D, _, _, hfin, hgal, hsplit, _⟩ := hp
  let : FiniteDimensional K D := hfin
  let : IsGalois K D := hgal
  obtain ⟨n, Es, ⟨e⟩⟩ := inducedTorusWeilDecomposition K D Q hsplit hQ
  have hFpqc := fieldExtension_fpqc K L
  let : IsAffineHom (GaloisCocycle.cover K L).hom :=
    inferInstanceAs (IsAffineHom (algebraBaseMap K L))
  let : Flat (GaloisCocycle.cover K L).hom := hFpqc.2.1
  let : Surjective (GaloisCocycle.cover K L).hom := hFpqc.1
  exact Cocycle.isTrivial_of_weilPresentation_of_semilocal
    (A := CommRingCat.of K) (B := CommRingCat.of (∀ j, Es j)) ξ
    (Langlands.CommGroupScheme.groupIso e)

/-- If `τ.map φ` is trivial, so is `τ.map (φ ≫ ψ)`. -/
theorem isTrivial_map_comp {S : Scheme.{u}} {G H H' : GroupScheme S} {U : Over S}
    {τ : Cocycle G U} {φ : G ⟶ H} (h : (τ.map φ).IsTrivial) (ψ : H ⟶ H') :
    (τ.map (φ ≫ ψ)).IsTrivial := by
  obtain ⟨c, hc⟩ := h.map ψ
  refine ⟨c, fun a b => ?_⟩
  rw [← hc]
  rfl

end TypeE7MaximalTorusCocycleOrder

open TypeE7MaximalTorusCocycleOrder in
/-- **Torus cocycles of simply connected groups of type `E₇`.** For a maximal torus `T` of a
simply connected group of type `E₇`, the endomorphism `36 • 𝟙 T` factors through an induced
torus, so the `36`-th power of every cocycle of `T` is trivial: one may take `a = b = 2`. -/
theorem typeE7MaximalTorusCocycleOrder : TypeE7MaximalTorusCocycleOrderStatement.{u} := by
  intro K _ _ G _ _ d e hsc _ hcartan T i hi L _ _ _ _ τ
  refine ⟨2, 2, ?_⟩
  classical
  have hG : IsConnectedReductive G := d.isSemisimple.isConnectedReductive
  -- Galois pinning data over a finite Galois splitting field `E` of `T`, with torus `T`.
  obtain ⟨E, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting K T.toGrp hi.1
  let d' := GaloisPinningData.ofSplittingField hG T i hi E hsplit
  -- Lift to the separable closure and compare with the pinning data of the Tits index.
  let ι : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let : Algebra E (SeparableClosure K) := ι.toRingHom.toAlgebra
  have hc : algebraBaseMap E (SeparableClosure K) ≫ algebraBaseMap K E =
      algebraBaseMap K (SeparableClosure K) := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg Subtype.val (ι.commutes x)
  obtain ⟨pd, e₁, -, -⟩ := StarActionFiniteStage.exists_lift d' hc
  obtain ⟨-, -, e₂, -, -, -, -⟩ :=
    StarActionIndependence.starActionIndependence K (SeparableClosure K) G d.pinning pd
  -- The Casimir identity for the pinning data of the Tits index.
  let P₀ := d.pinning.toSplitPinning.rootDatum
  have : P₀.IsReduced := d.pinning.isReduced
  let : Fintype d.pinning.toSplitPinning.rootIndex := Fintype.ofFinite _
  let : Fintype pd.toSplitPinning.rootIndex := Fintype.ofFinite _
  let : Fintype d'.toSplitPinning.rootIndex := Fintype.ofFinite _
  let s : Fin 7 → d.pinning.rootIndex := fun k => (e.symm k).val
  have hA : ∀ a b, P₀.pairing (s a) (s b) = CartanMatrix.E 7 a b := by
    intro a b
    have := hcartan (e.symm a) (e.symm b)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this
  have hscE := isSimplyConnectedFieldExtension K (SeparableClosure K) G hsc
  have hspan : P₀.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpanIndependent (SeparableClosure K) _ hscE _
      d.pinning.isSplitTorus _ d.pinning.isMaximalTorus _ d.pinning.rootDatum
      d.pinning.isRootDatum d.pinning.isReduced
  have h₀ := E7Casimir.sum_toLinearMap_coroot_smul_root hA d.pinning.base
    (fun k => (e.symm k).2) (fun a ha => ⟨e ⟨a, ha⟩, by simp [s]⟩) hspan
  have h₁ := E7Casimir.sum_toLinearMap_coroot_smul_root_of_equiv e₂ 36 h₀
  have h₂ := E7Casimir.sum_toLinearMap_coroot_smul_root_of_equiv_symm e₁ 36 h₁
  -- Factor `36 • 𝟙 T` through an induced torus.
  obtain ⟨Q, f, g, hQ, hfg⟩ := exists_inducedTorus_comp_eq_zsmul d' 36 h₂
  have hτ : (τ.map (CommGroupScheme.groupHom f)).IsTrivial :=
    isTrivial_of_isInducedTorus K L Q hQ _
  have h36 : ((2 ^ 2 * 3 ^ 2 : ℕ) • 𝟙 T) = f ≫ g := by
    rw [hfg, ← natCast_zsmul]
    rfl
  rw [h36]
  exact isTrivial_map_comp hτ (CommGroupScheme.groupHom g)

end Langlands.GroupScheme
