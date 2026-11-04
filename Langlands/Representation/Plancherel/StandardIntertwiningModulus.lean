import Langlands.Representation.Plancherel.StandardIntertwiningTarget
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusTarget

/-! # Actual intersection characters for the standard intertwiner -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General
open Aubert.General.CorrectedFiltration

universe uG uI

section Intersection

variable {G : Type uG} [Group G] [TopologicalSpace G] (U U' : Subgroup G)

/-- Identify the actual intersection inside `U'` with the ambient intersection,
without assuming either radical contains the other. -/
def intersectionContinuousEquiv : U.subgroupOf U' ≃ₜ* (U ⊓ U' : Subgroup G) where
  toFun x := ⟨((x : U') : G), x.property, (x : U').property⟩
  invFun x := ⟨⟨(x : G), x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem intersectionContinuousEquiv_apply (x : U.subgroupOf U') :
    (intersectionContinuousEquiv U U' x : G) = ((x : U') : G) := rfl

@[simp]
theorem intersectionContinuousEquiv_symm_apply (x : (U ⊓ U' : Subgroup G)) :
    (((intersectionContinuousEquiv U U').symm x : U') : G) = (x : G) := rfl

end Intersection

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P P' M U U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))

include h h' in
omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The common Levi normalizes the actual ambient intersection. -/
theorem levi_le_normalizer_intersection :
    M ≤ Subgroup.normalizer (U ⊓ U' : Set G) :=
  (le_inf h.levi_le_normalizer h'.levi_le_normalizer).trans
    Subgroup.inf_normalizer_le_normalizer_inf

variable [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]

/-- The Haar modulus of the restricted actual conjugation is exactly the
ambient intersection character; the supplied Borel structures are retained. -/
theorem intersection_haarChar (m : M) :
    letI : LocallyCompactSpace U' := hU'.locallyCompactSpace
    letI : LocallyCompactSpace (U.subgroupOf U') :=
      (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
    mulEquivHaarChar
        (QuotientIntegration.subgroupAutomorphism (U.subgroupOf U')
          (HaarModulus.normalizerConj U' ⟨m, h'.levi_le_normalizer m.property⟩)
          (intersection_conj_invariant h U' h'.levi_le_normalizer m)) =
      (HaarModulus.closedRestrictCharacter (U ⊓ U') (hU.inter hU') M
        (levi_le_normalizer_intersection h h') m : ℝ≥0) := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  exact mulEquivHaarChar_eq_closedNormalizerCharacter (U ⊓ U') (hU.inter hU')
    ⟨m, levi_le_normalizer_intersection h h' m.property⟩
    (intersectionContinuousEquiv U U') _ (fun _ => rfl)

/-- The analytic squared-modulus premise is equivalent to the same identity
entirely in ambient closed-subgroup characters. -/
theorem squaredModulusCompatibility_iff :
    SquaredModulusCompatibility h hU h' hU' ↔
      ∀ m : M,
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m : ℝ≥0) *
          (HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (U ⊓ U') (hU.inter hU') M
          (levi_le_normalizer_intersection h h') m : ℝ≥0) ^ 2 := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  constructor
  · intro hs m
    simpa only [intersection_haarChar h hU h' hU'] using hs m
  · intro hs m
    rw [intersection_haarChar h hU h' hU']
    exact hs m

section Conjugate

variable {PK MK UK : Subgroup G}
  (hK : IsSemidirectDecomposition PK MK UK) (hUK : IsClosed (UK : Set G))
  (n : G) (hMM' : ∀ x : G, x ∈ M ↔ n⁻¹ * x * n ∈ MK)
  (hUU' : ∀ x : G, x ∈ U' ↔ n⁻¹ * x * n ∈ UK)

include hUU' in
omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] in
/-- An actual conjugate target radical gives exactly the shared orbit
intersection, as equality of ambient subgroups. -/
theorem intersection_eq_orbitUnipotentIntersection :
    U ⊓ U' = orbitUnipotentIntersection U UK n := by
  ext x
  rw [Subgroup.mem_inf, mem_orbitUnipotentIntersection]
  exact and_congr Iff.rfl (hUU' x)

include hUU' in
/-- Consume the shared orbit's exact pointwise squared-modulus formula after
proving both the target-radical and the actual intersection comparisons. -/
theorem squaredModulusCompatibility_of_orbit
    (hsq : ∀ m : M,
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m : ℝ≥0) *
        (HaarModulus.closedRestrictCharacter UK hUK MK hK.levi_le_normalizer
          (conjugationEquiv n hMM' m) : ℝ≥0) =
      (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection U UK n)
        (isClosed_orbitUnipotentIntersection hU hUK n) M
        (levi_le_normalizer_orbitUnipotentIntersection h hK n hMM') m : ℝ≥0) ^ 2) :
    SquaredModulusCompatibility h hU h' hU' := by
  apply (squaredModulusCompatibility_iff h hU h' hU').mpr
  intro m
  rw [closedRestrictCharacter_conj n hUU' hMM' hUK hU'
    hK.levi_le_normalizer h'.levi_le_normalizer]
  have he := intersection_eq_orbitUnipotentIntersection (U := U) n hUU'
  simpa only [he] using hsq m

end Conjugate

section Family

variable {ι : Type uI}
  (P₀ M₀ U₀ : Finset ι → Subgroup G)
  (h₀ : ∀ J, IsSemidirectDecomposition (P₀ J) (M₀ J) (U₀ J))
  (hclosed : ∀ J, IsClosed (U₀ J : Set G))
  (T : Subgroup G)
  [Fintype (Group.RelativeWeyl.Weyl T)] [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (Group.RelativeWeyl.Weyl T))

/-- Specialize the existing shared orbit target to the actual standard
intertwiner. The shared identity remains an explicit premise. -/
theorem squaredModulusCompatibility_of_orbitTarget
    (hsq : OrbitSquaredModulusTarget P₀ M₀ U₀ h₀ hclosed T cs)
    (I : Finset ι) (j : ℕ) (hj : j < (Aubert.Support.rankOrderedList cs.length).length)
    (n : Group.RelativeWeyl.normalizer T)
    (hn : (QuotientGroup.mk n : Group.RelativeWeyl.Weyl T) =
      (Aubert.Support.rankOrderedElement cs.length j hj)⁻¹)
    (K : Finset ι) (hMK : ∀ x : G, x ∈ M₀ I ↔ (n : G)⁻¹ * x * n ∈ M₀ K)
    {P' U' : Subgroup G} (h' : IsSemidirectDecomposition P' (M₀ I) U')
    (hU' : IsClosed (U' : Set G))
    (hUU' : ∀ x : G, x ∈ U' ↔ (n : G)⁻¹ * x * n ∈ U₀ K)
    [MeasurableSpace ((U₀ I).subgroupOf U')] [BorelSpace ((U₀ I).subgroupOf U')] :
    SquaredModulusCompatibility (h₀ I) (hclosed I) h' hU' :=
  squaredModulusCompatibility_of_orbit (h₀ I) (hclosed I) h' hU'
    (h₀ K) (hclosed K) (n : G) hMK hUU' (hsq I j hj n hn K hMK)

end Family

end Langlands.Plancherel.StandardIntertwining
