import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermThresholdMinimalLeviProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermRegionComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermExistenceProof
import Langlands.Representation.Plancherel.NormalizedCompactPicture

/-! # The uniform constant-term threshold for the actual orbit coefficients

Proof of `RationalOrbitConstantTermThresholdStatement` (Waldspurger, Proposition I.4.3 and I.5,
as used on printed pp. 299 and 303). The threshold of
`exists_constantTerm_dimension_threshold` depends only on a basis member `K₂` and on a bound
for the dimension of the `K₂`-fixed vectors. All orbit coefficients `f_ω` are bi-invariant under
one compact open subgroup, so they lie in the span of coefficients of fixed vectors and fixed
functionals of a fixed basis member, and the induced representations `I_P^G(π ⊗ χ)` of the
orbit all restrict to the same compact picture on `K`, so their `K₂`-fixed vectors have one
common dimension.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Averaging

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The representation `g ↦ (x ↦ (j ↦ ρ(g) (x j)))` on `Idx`-tuples of vectors. -/
def piRepresentation (ρ : Representation ℂ G V) (Idx : Type*) : Representation ℂ G (Idx → V) where
  toFun g := LinearMap.pi fun j => (ρ g).comp (LinearMap.proj j)
  map_one' := LinearMap.ext fun x => funext fun j => by simp
  map_mul' g h := LinearMap.ext fun x => funext fun j => by simp [Module.End.mul_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem piRepresentation_apply (ρ : Representation ℂ G V) (Idx : Type*) (g : G)
    (x : Idx → V) (j : Idx) : piRepresentation ρ Idx g x j = ρ g (x j) := rfl

omit [IsTopologicalGroup G] in
/-- Tuples of smooth vectors indexed by a finite type are smooth. -/
theorem isSmooth_piRepresentation (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (Idx : Type*)
    [Finite Idx] : IsSmooth (piRepresentation ρ Idx) := by
  classical
  have := Fintype.ofFinite Idx
  intro x
  choose U hU using fun j => hρ (x j)
  refine ⟨Finset.univ.inf U, fun k => funext fun j => ?_⟩
  have hk : (k : G) ∈ U j := Finset.inf_le (f := U) (Finset.mem_univ j) k.property
  exact hU j ⟨k, hk⟩

/-- The `j`-th projection, as an intertwining map. -/
def piProjection (ρ : Representation ℂ G V) (Idx : Type*) (j : Idx) :
    (piRepresentation ρ Idx).IntertwiningMap ρ where
  toLinearMap := LinearMap.proj j
  isIntertwining' _ := LinearMap.ext fun _ => rfl

/-- **Averaging a tuple.** If a linear form `L` on `Idx`-tuples is constant on the `K`-orbit of a
tuple `x`, it takes the same value at the tuple of the `K`-averages of the entries of `x`. -/
theorem map_averageMap_pi_of_forall_eq (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {Idx : Type*} [Finite Idx] (x : Idx → V)
    (L : (Idx → V) →ₗ[ℂ] ℂ) (hL : ∀ k ∈ K, L (fun j => ρ k (x j)) = L x) :
    L (fun j => Compact.averageMap ρ hρ K hK (x j)) = L x := by
  have hpi := isSmooth_piRepresentation ρ hρ Idx
  have h1 := Jacquet.map_averageMap_of_forall_eq (piRepresentation ρ Idx) hpi K hK L x (L x)
    (fun k => hL k k.property)
  have h2 : Compact.averageMap (piRepresentation ρ Idx) hpi K hK x =
      fun j => Compact.averageMap ρ hρ K hK (x j) := by
    funext j
    exact LinearMap.congr_fun (Compact.averageMap_commute (piRepresentation ρ Idx) ρ hpi hρ K hK
      (piProjection ρ Idx j)) x
  rw [← h2]
  exact h1

/-- **Bi-invariant coefficients are coefficients of fixed vectors.** A function in Waldspurger's
coefficient space `A(π)` of a smooth representation that is invariant under left and right
translation by a compact open subgroup `K` lies in the span of the coefficients
`x ↦ ℓ(π(x) v)` with `v` and `ℓ` both fixed by `K`. -/
theorem mem_span_fixedCoefficients_of_biInvariant {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : SmoothRep.{0, u, uV} ℂ G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) {f : G → ℂ} (hf : f ∈ coefficientFunctionSpace A)
    (hinv : ∀ k ∈ K, ∀ l ∈ K, ∀ g, f (k * g * l) = f g) :
    f ∈ Submodule.span ℂ {φ : G → ℂ | ∃ v ∈ fixedVectors A.representation K.toSubgroup,
      ∃ ℓ ∈ fixedVectors (smoothContragredient A.representation) K.toSubgroup,
        φ = fun x => smoothDualPairing A.representation ℓ (A.representation x v)} := by
  classical
  set ρ := A.representation with hρdef
  have hρ : IsSmooth ρ := A.isSmooth
  have hρ' : IsSmooth (smoothContragredient ρ) := isSmooth_smoothContragredient ρ
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).mp hf
  choose v hv using hc
  let Idx := c.support
  let x : Idx → A := fun j => v j.1
  let lam : Idx → SmoothDual ρ := fun j => j.1
  have hf' : ∀ g, f g = ∑ j : Idx, smoothDualPairing ρ (lam j) (ρ g (x j)) := by
    intro g
    rw [← hsum, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hv j.1]
    rfl
  -- right average
  let xbar : Idx → A := fun j => Compact.averageMap ρ hρ K hK (x j)
  have h1 : ∀ g, f g = ∑ j : Idx, smoothDualPairing ρ (lam j) (ρ g (xbar j)) := by
    intro g
    let L : (Idx → A) →ₗ[ℂ] ℂ :=
      ∑ j : Idx, ((smoothDualPairing ρ (lam j)).comp (ρ g)).comp (LinearMap.proj j)
    have hL : ∀ y : Idx → A, L y = ∑ j : Idx, smoothDualPairing ρ (lam j) (ρ g (y j)) := by
      intro y
      simp [L]
    have key := map_averageMap_pi_of_forall_eq ρ hρ K hK x L (fun k hk => by
      rw [hL, hL, ← hf' g]
      have e : ∀ j : Idx, smoothDualPairing ρ (lam j) (ρ g (ρ k (x j))) =
          smoothDualPairing ρ (lam j) (ρ (g * k) (x j)) := by
        intro j
        rw [map_mul, Module.End.mul_apply]
      simp only [e]
      rw [← hf' (g * k)]
      simpa using hinv 1 K.one_mem k hk g)
    rw [hL, hL] at key
    rw [hf' g]
    exact key.symm
  -- left average
  let lbar : Idx → SmoothDual ρ := fun j => Compact.averageMap (smoothContragredient ρ) hρ' K hK
    (lam j)
  have h2 : ∀ g, f g = ∑ j : Idx, smoothDualPairing ρ (lbar j) (ρ g (xbar j)) := by
    intro g
    let L : (Idx → SmoothDual ρ) →ₗ[ℂ] ℂ :=
      ∑ j : Idx, ((smoothDualPairing ρ).flip (ρ g (xbar j))).comp (LinearMap.proj j)
    have hL : ∀ y : Idx → SmoothDual ρ, L y = ∑ j : Idx, smoothDualPairing ρ (y j) (ρ g (xbar j)) := by
      intro y
      simp [L]
    have key := map_averageMap_pi_of_forall_eq (smoothContragredient ρ) hρ' K hK lam L
      (fun k hk => by
        rw [hL, hL, ← h1 g]
        have e : ∀ j : Idx, smoothDualPairing ρ (smoothContragredient ρ k (lam j)) (ρ g (xbar j)) =
            smoothDualPairing ρ (lam j) (ρ (k⁻¹ * g) (xbar j)) := by
          intro j
          rw [smoothDualPairing_action, map_mul, Module.End.mul_apply]
        simp only [e]
        rw [← h1 (k⁻¹ * g)]
        simpa using hinv k⁻¹ (K.inv_mem hk) 1 K.one_mem g)
    rw [hL, hL] at key
    rw [h1 g]
    exact key.symm
  have hfeq : f = ∑ j : Idx, fun y => smoothDualPairing ρ (lbar j) (ρ y (xbar j)) := by
    funext g
    rw [h2 g, Finset.sum_apply]
  rw [hfeq]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
  exact ⟨xbar j, Compact.averageMap_mem_fixedVectors ρ hρ K hK _, lbar j,
    Compact.averageMap_mem_fixedVectors _ hρ' K hK _, rfl⟩

end Averaging

section Dimension

/-- An equivalence between the restriction of `σ` to a subgroup `K` and a representation `τ`
of `K` preserves the dimension of the vectors fixed by any `H ≤ K`. -/
theorem finrank_fixedVectors_eq_of_equiv_comp {G : Type*} [Group G] {K H : Subgroup G}
    (hHK : H ≤ K) {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (τ : Representation ℂ K W) (e : Representation.Equiv (σ.comp K.subtype) τ) :
    Module.finrank ℂ (fixedVectors σ H) =
      Module.finrank ℂ (fixedVectors τ (H.comap K.subtype)) := by
  have hint : ∀ (k : K) (v : V), e.toLinearEquiv (σ (k : G) v) = τ k (e.toLinearEquiv v) :=
    fun k v => LinearMap.congr_fun (e.isIntertwining' k) v
  have hmem : ∀ v, v ∈ fixedVectors σ H ↔
      e.toLinearEquiv v ∈ fixedVectors τ (H.comap K.subtype) := by
    intro v
    constructor
    · intro hv k
      change τ (k : K) (e.toLinearEquiv v) = e.toLinearEquiv v
      rw [← hint]
      exact congrArg _ (hv ⟨((k : K) : G), k.property⟩)
    · intro hv g
      have hgK : (g : G) ∈ K := hHK g.property
      apply e.toLinearEquiv.injective
      change e.toLinearEquiv (σ (g : G) v) = e.toLinearEquiv v
      have h := hint ⟨g, hgK⟩ v
      rw [h]
      exact hv ⟨⟨g, hgK⟩, g.property⟩
  refine LinearEquiv.finrank_eq (e.toLinearEquiv.ofSubmodules _ _ ?_)
  ext w
  rw [Submodule.mem_map_equiv, hmem, LinearEquiv.apply_symm_apply]

end Dimension

section Threshold

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)

/-- One compact open subgroup `H ≤ K` makes every orbit coefficient `f_ω = E^G_P ψ_ω`
bi-invariant, simultaneously for all `ω ∈ O` (the published
`unitaryOrbitCoefficientMap_biInvariant` on the actual data). -/
theorem exists_rationalInducedOrbitCoefficientMap_biInvariant
    (ψ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    ∃ H : OpenSubgroup (rationalPoints G), H ≤ K ∧ IsCompact (H : Set (rationalPoints G)) ∧
      ∀ (ω : discreteSeriesOrbit C hC mu (RationalPointFamily.leviRationalNormCharacters i ν I)
          (discreteSeriesClass C hC mu π hsq)) (k l : H) (g : rationalPoints G),
        rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq ψ ω
            ((k : rationalPoints G) * g * (l : rationalPoints G)) =
          rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq ψ ω g := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := unitaryOrbitCoefficientMap_biInvariant (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    C hC mu hsq (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv ψ
  with_reducible_and_instances exact h

set_option maxHeartbeats 800000 in
/-- **The uniform actual-orbit constant-term threshold** (Waldspurger, Proposition I.4.3 and
I.5): `RationalOrbitConstantTermThresholdStatement` holds for all its data. -/
theorem rationalOrbitConstantTermThreshold :
    RationalOrbitConstantTermThresholdStatement hG hi hν I hKc hPK π C hC mu hsq I' hA := by
  classical
  intro ζ hζ K0 B hK0o hK0c hB hmem hsim hfin hlevi ψ
  have hJ : RationalPointFamily.rootSet i ν I' ⊆ simpleRelativeRoots i ν :=
    RationalPointFamily.rootSet_subset i ν I'
  -- the simultaneous basis data
  obtain ⟨B₂, hB₂, hBJ⟩ := hsim
  have hdata : ∀ J : Set (characterLattice S),
      ∃ (A' : CommGroupScheme (Spec (CommRingCat.of F))) (q' : A'.toGrp ⟶ S.toGrp),
        J ⊆ simpleRelativeRoots i ν →
          IsCompatibleStandardSplitComponent i ν J A' q' ∧
            ∀ K' ∈ B₂, StandardParabolicBasisMember i ν J q' K' := by
    intro J
    by_cases hJ' : J ⊆ simpleRelativeRoots i ν
    · obtain ⟨-, A', q', h1, h2⟩ := hBJ J hJ'
      exact ⟨A', q', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨S, 𝟙 _, fun h => absurd h hJ'⟩
  choose A₂ q₂ hAq using hdata
  have hζex : ∀ J : Set (characterLattice S), ∃ ζ' : cocharacterLattice S,
      J ⊆ simpleRelativeRoots i ν → IsStandardCocharacter i ν J ζ' := by
    intro J
    by_cases hJ' : J ⊆ simpleRelativeRoots i ν
    · obtain ⟨ζ', hζ'⟩ := (standardCocharacter F G hG S i hi ν hν J hJ').1
      exact ⟨ζ', fun _ => hζ'⟩
    · exact ⟨0, fun h => absurd h hJ'⟩
  choose ζ₂ hζ₂ using hζex
  -- one compact open subgroup for the whole orbit
  obtain ⟨H, hHK, -, hH⟩ :=
    exists_rationalInducedOrbitCoefficientMap_biInvariant hG hi hν I hKc hPK π C hC mu hsq ψ
  obtain ⟨K₁, hK₁B, hK₁H⟩ := hB₂.2.mem_iff.mp H.mem_nhds_one
  obtain ⟨K₂, -, hK₂le, hK₂⟩ := exists_constantTerm_dimension_threshold.{u, max u uV} hG hi hν
    hB₂ A₂ q₂ (fun J hJ' => (hAq J hJ').1) (fun J hJ' => (hAq J hJ').2) ζ₂ hζ₂ hK0c
    (hlevi ∅ (Set.empty_subset _)) hJ hA hζ hK₁B
  have hK₂K : K₂ ≤ (K : Subgroup (rationalPoints G)) := fun x hx => hHK (hK₁H (hK₂le hx))
  -- the common dimension of the `K₂`-fixed vectors of the compact picture
  obtain ⟨t, ht, hthr⟩ := hK₂ (Module.finrank ℂ (fixedVectors
    (Induction.smoothInduced
      ((standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I)).comap
        K.toSubgroup.subtype)
      (compactPictureInducingRepresentation
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        K π.obj))
    (K₂.comap K.toSubgroup.subtype)))
  refine ⟨t, ht, fun ω m hm => ?_⟩
  obtain ⟨χ, hχ⟩ := ω.property
  let R : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π :=
    ⟨IrreducibleAdmissibleRep.twist
      (unitaryUnramifiedInclusion (RationalPointFamily.leviRationalNormCharacters i ν I)
        χ).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker (RationalPointFamily.leviRationalNormCharacters i ν I)
        (unitaryUnramifiedInclusion (RationalPointFamily.leviRationalNormCharacters i ν I) χ)) π,
      χ, rfl⟩
  have hω : unitaryOrbitRepresentativeDiscreteSeriesOrbit
      (RationalPointFamily.leviRationalNormCharacters i ν I) π C hC mu hsq R = ω :=
    Subtype.ext hχ
  have hbi := hH ω
  rw [← hω] at hbi ⊢
  unfold rationalOrbitConstantTerm
  rw [rationalInducedOrbitCoefficientMap_representative hG hi hν I hKc hPK π C hC mu hsq ψ R]
    at hbi ⊢
  have := compactSpace_leftQuotient_standardParabolicPoints_rootSet hG hi hν I hKc hPK
  have hX := normalizedInductionFunctor_obj_isAdmissible
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    R.val.obj R.val.property.2
  have hf := rationalInducedCoefficientMap_mem_coefficientFunctionSpace hG hi hν I hKc hPK
    R.val.obj R.val.property.2 (ψ.val R)
  have hspan := mem_span_fixedCoefficients_of_biInvariant _ (basisOpenSubgroup hB₂ hK₁B)
    (hB₂.1 K₁ hK₁B).2.2.2 hf
    (fun k hk l hl g => hbi ⟨k, hK₁H hk⟩ ⟨l, hK₁H hl⟩ g)
  have hd := (finrank_fixedVectors_eq_of_equiv_comp hK₂K _ _
    (unramifiedNormalizedInductionCompactEquiv
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)) K
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
      (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
      (RationalPointFamily.leviRationalNormCharacters i ν I)
      (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
      (unitaryUnramifiedInclusion (RationalPointFamily.leviRationalNormCharacters i ν I) χ)
      π.obj)).le
  exact hthr _ hX hd _ hspan m hm

end Threshold

end Langlands.HarishChandraSchwartz
