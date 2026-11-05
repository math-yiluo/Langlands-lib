import Langlands.Representation.Plancherel.StandardIntertwiningScalarDomain
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Twist.SmoothPartDefinitions

/-! # Scalar Iwasawa bounds for the actual standard quotient integral -/

noncomputable section

open MeasureTheory

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- The actual quotient integrand is locally constant, without any topology
on the inducing carrier. -/
theorem integrand_isLocallyConstant (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    IsLocallyConstant (integrand h hU U' A g f) := by
  intro s
  apply (isQuotientMap_quotient_mk'
    (s := QuotientGroup.rightRel (U.subgroupOf U'))).isCoinducing.isOpen_preimage.mp
  exact ((eval_isLocallyConstant P (leviInflatedInducingRepresentation h hU A) f).comp_continuous
    (continuous_subtype_val.mul continuous_const)) s

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- Smooth scalar tests are strongly measurable for every Borel quotient
measure, even when the ambient group is not second countable. -/
theorem scalarIntegrand_aestronglyMeasurable (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual A.representation) :
    AEStronglyMeasurable (fun q => ℓ.val (integrand h hU U' A g f q)) ν :=
  ((integrand_isLocallyConstant h hU U' A g f).comp ℓ.val).continuous.aestronglyMeasurable

omit [BorelSpace (QuotientSpace (U := U) U')] in
/-- All evaluation points reduce to the identity by the actual source right
action. This requires no target modulus comparison or representability. -/
theorem scalarDomain_eq_top_iff_integrable_at_one :
    scalarDomain h hU U' A ν = ⊤ ↔
      ∀ (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
        (ℓ : SmoothDual A.representation),
        MeasureTheory.Integrable (fun q => ℓ.val (integrand h hU U' A 1 f q)) ν := by
  constructor
  · intro ht f ℓ
    have hf : f ∈ scalarDomain h hU U' A ν := by rw [ht]; trivial
    exact hf 1 ℓ
  · intro hi
    apply top_unique
    intro f _ g ℓ
    have hf := hi
      (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation g f) ℓ
    simpa only [integrand_right_action, one_mul] using hf

variable (K : OpenSubgroup G)

/-- The source half-character times a common Levi coefficient envelope,
evaluated on supplied parabolic coordinates of quotient points. No
measurability or integrability of these coordinates is implicit. -/
def iwasawaWeight (ξ : M → ℝ) (p : QuotientSpace (U := U) U' → P) :
    QuotientSpace (U := U) U' → ℝ :=
  fun q =>
    ‖(HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
      (h.projection (p q)) : ℂ)‖ * ξ (h.projection (p q))

omit [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compactness gives finitely many actual inducing vectors, so one common
Levi coefficient envelope bounds every parabolic-compact factorization of
the actual scalar quotient integrand. -/
theorem scalarIntegrand_bound (hK : IsCompact (K : Set G))
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual A.representation) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : G) (u' : U') (p : P) (k : K),
      (u' : G) * g = (p : G) * (k : G) →
      ‖ℓ.val (integrand h hU U' A g f (Quotient.mk _ u'))‖ ≤
        C * (‖(HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
          (h.projection p) : ℂ)‖ * ξ (h.projection p)) := by
  let v : K → A := fun k =>
    eval P (leviInflatedInducingRepresentation h hU A) f (k : G)
  have hv : (Set.range v).Finite := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact ((eval_isLocallyConstant P (leviInflatedInducingRepresentation h hU A) f).comp_continuous
      continuous_subtype_val).range_finite
  choose c hcpos hc using fun w : A => hcoeff w ℓ
  obtain ⟨B, hB⟩ := (hv.image c).bddAbove
  let C := max 1 B
  refine ⟨C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro g u' p k he
  have hb : ‖ℓ.val (A.representation (h.projection p) (v k))‖ ≤
      C * ξ (h.projection p) :=
    (hc (v k) (h.projection p)).trans
      (mul_le_mul_of_nonneg_right
        ((hB ⟨v k, ⟨k, rfl⟩, rfl⟩).trans (le_max_right 1 B))
        (hξ (h.projection p)))
  rw [integrand_mk, he,
    eval_covariant P (leviInflatedInducingRepresentation h hU A) f p (k : G)]
  change ‖ℓ.val
    ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
      (h.projection p) : ℂ) • A.representation (h.projection p) (v k))‖ ≤ _
  rw [map_smul, norm_smul]
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)

/-- One integrable scalar weight on the actual quotient gives convergence
of every source function at every evaluation point. The supplied
factorizations may use any representative of each actual left coset. -/
theorem scalarDomain_eq_top_of_integrable_iwasawaWeight
    (hK : IsCompact (K : Set G))
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (p : QuotientSpace (U := U) U' → P) (k : QuotientSpace (U := U) U' → K)
    (hfactor : ∀ q, ∃ u' : U', Quotient.mk _ u' = q ∧
      (u' : G) = (p q : G) * (k q : G))
    (hweight : MeasureTheory.Integrable (iwasawaWeight h hU U' ξ p) ν) :
    scalarDomain h hU U' A ν = ⊤ := by
  apply (scalarDomain_eq_top_iff_integrable_at_one h hU U' A ν).mpr
  intro f ℓ
  obtain ⟨C, hC, hb⟩ := scalarIntegrand_bound h hU U' A K hK ξ hξ hcoeff f ℓ
  apply (hweight.const_mul C).mono'
    (scalarIntegrand_aestronglyMeasurable h hU U' A ν 1 f ℓ)
  apply Filter.Eventually.of_forall
  intro q
  obtain ⟨u', hu', he⟩ := hfactor q
  rw [← hu']
  exact hb 1 u' (p (Quotient.mk _ u')) (k (Quotient.mk _ u'))
    (by simpa only [mul_one, hu'] using he)

end Langlands.Plancherel.StandardIntertwining
