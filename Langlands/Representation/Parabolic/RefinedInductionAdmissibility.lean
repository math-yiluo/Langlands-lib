import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Twist.AdmissibilityProof

/-! Admissibility of actual normalized induction inside a product Levi. -/

noncomputable section

namespace Langlands

universe uH uG

/-- A homomorphism of topological groups with a continuous right inverse is open.
The right inverse need not be a homomorphism. -/
theorem isOpenMap_of_continuous_rightInverse {H : Type uH} {G : Type uG}
    [Group H] [Group G] [TopologicalSpace H] [TopologicalSpace G] [ContinuousMul H]
    (q : H →* G) (s : G → H) (hs : Continuous s) (hqs : Function.RightInverse s q) :
    IsOpenMap q := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, hu, rfl⟩
  let f : G → H := fun g => u * (s (q u))⁻¹ * s g
  have hf : Continuous f := continuous_const.mul hs
  have hfu : f (q u) = u := by simp [f]
  have hmem : f ⁻¹' U ∈ nhds (q u) :=
    hf.continuousAt.preimage_mem_nhds (by rw [hfu]; exact hU.mem_nhds hu)
  refine Filter.mem_of_superset hmem fun g hg => ⟨f g, hg, ?_⟩
  simp only [f, map_mul, map_inv, hqs g, hqs (q u), mul_inv_cancel, one_mul]

end Langlands

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual refined Levi projection is an open map. -/
theorem isOpenMap_refinedLeviProjection :
    letI := T.topology
    IsOpenMap (refinedLeviProjection F.Carrier B S) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  exact isOpenMap_of_continuous_rightInverse (refinedLeviProjection F.Carrier B S)
    (refinedLeviSection F.Carrier B S) (refinedLeviSectionContinuous F.Carrier B S).continuous
    (refinedLeviProjection_section F.Carrier B S)

/-- Admissibility is preserved and reflected by inflation through the actual
refined Levi projection. -/
theorem isAdmissible_refinedInflation_iff {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    IsAdmissible (σ.comp (refinedLeviProjection F.Carrier B S)) ↔ IsAdmissible σ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact isAdmissible_comp_iff_of_open_surjective σ (refinedLeviProjection F.Carrier B S)
    (refinedLeviProjectionContinuous F.Carrier B S).continuous
    (isOpenMap_refinedLeviProjection T B S)
    (fun m => ⟨refinedLeviSection F.Carrier B S m, refinedLeviProjection_section F.Carrier B S m⟩)

/-- Every right coset of the actual refined parabolic meets the product of the
integral groups of the outer blocks. -/
theorem refinedQuotientMap_image_integralRange :
    letI := T.valuativeRel
    Induction.quotientMap (refinedParabolic F.Carrier B S) ''
      (Set.univ.pi fun i =>
        (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) (B.size i) :
          Set (GeneralLinear (B.size i) F.Carrier))) = Set.univ := by
  let := T.valuativeRel
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using Quotient.inductionOn with
  | h g =>
    choose k hk hup using fun i =>
      Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F.Carrier) (B.size i) (g i)
    refine ⟨fun i => (k i)⁻¹, fun i _ => inv_mem (hk i), Quotient.sound ?_⟩
    change QuotientGroup.rightRel _ (fun i => (k i)⁻¹) g
    rw [QuotientGroup.rightRel_apply, mem_refinedParabolic]
    intro i
    have h := (S i).mem_parabolic_of_isUpperTriangular _ (hup i)
    simpa only [Pi.mul_apply, Pi.inv_apply, inv_inv] using h

end Local

/-- The actual coset space of a refined parabolic in a product Levi is compact,
for every block shape and refinement, including empty blocks and rank zero. -/
theorem refinedParabolicQuotientCompact {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    CompactSpace (Induction.LeftQuotient (refinedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  refine ⟨?_⟩
  rw [← refinedQuotientMap_image_integralRange T B S]
  exact (isCompact_univ_pi fun i => isCompact_integralRange T (B.size i)).image
    continuous_quotient_mk'

/-- Actual normalized refined induction preserves admissibility. -/
theorem normalizedRefinedInductionAdmissibility {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    IsAdmissible σ → IsAdmissible (T.normalizedRefinedInduced B S σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  intro hσ
  have hTwisted : IsAdmissible (twist (T.refinedParabolicHalfModulus B S)
      (σ.comp (refinedLeviProjection F.Carrier B S))) :=
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B S)).mpr
      ((isAdmissible_refinedInflation_iff T B S σ).mpr hσ)
  have := refinedParabolicQuotientCompact F T B S
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _ _ hTwisted

/-- Admissibility clause for actual normalized refined induction: every
admissible complex representation of the refined Levi on a carrier `V`
induces to an admissible representation of the product Levi. -/
def RefinedInductionAdmissibilityClause {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) (V : Type uV) [AddCommGroup V] [Module ℂ V] : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  ∀ σ : Representation ℂ (refinedLevi F.Carrier B S) V,
    IsAdmissible σ → IsAdmissible (T.normalizedRefinedInduced B S σ)

/-- The admissibility clause holds for every refinement and carrier. -/
theorem refinedInductionAdmissibilityClause_holds {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    RefinedInductionAdmissibilityClause F T B S V :=
  fun σ => normalizedRefinedInductionAdmissibility F T B S σ

/-- Admissibility is unchanged by pulling back through the inverse of the actual
flattened Levi equivalence. -/
theorem isAdmissible_flattenedLeviTransport_iff {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ ((B.flatten S).Levi F.Carrier) V) :
    letI := T.topology
    IsAdmissible (ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) ↔
      IsAdmissible ρ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := (flattenedLeviEquivContinuous F.Carrier B S).symm
  exact isAdmissible_comp_iff_of_open_surjective ρ _ e.continuous
    e.toHomeomorph.isOpenMap e.surjective

/-- The admissibility clause of the refined cuspidal induction target: the
actual normalized refined induction of the transported Levi-cuspidal input is
admissible. -/
theorem refinedCuspidalInduction_isAdmissible {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)) :
    letI := T.topology
    CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      letI := T.leviTopologicalGroup B
      IsAdmissible (Rep.of (T.normalizedRefinedInduced B S
        (ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom))).ρ := by
  let := T.topology
  intro hω
  exact normalizedRefinedInductionAdmissibility F T B S _
    ((isAdmissible_flattenedLeviTransport_iff F T B S ω.ρ).mpr hω.1)

end Langlands.Parabolic
