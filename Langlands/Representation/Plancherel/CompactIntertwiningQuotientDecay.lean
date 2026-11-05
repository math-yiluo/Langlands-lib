import Langlands.Representation.Plancherel.CompactIntertwiningWeakRegularity
import Langlands.Representation.Plancherel.StandardIntertwiningTwistBounds

/-! # Convergence and local domination of standard integrals from quotient decay -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Filter
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uG uI uV

namespace StandardIntertwining

section Majorant

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)

/-- **Convergence from an integrable majorant.** The published Iwasawa reduction with the
integrability of the weight replaced by an integrable function bounding it. No measurability of
the weight or of the coordinates is needed. -/
theorem scalarDomain_eq_top_of_le_integrable
    (hK : IsCompact (K : Set G))
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (p : QuotientSpace (U := U) U' → P) (k : QuotientSpace (U := U) U' → K)
    (hfactor : ∀ q, ∃ u' : U', Quotient.mk _ u' = q ∧
      (u' : G) = (p q : G) * (k q : G))
    (W : QuotientSpace (U := U) U' → ℝ) (hW : Integrable W ν)
    (hle : ∀ q, iwasawaWeight h hU U' ξ p q ≤ W q) :
    scalarDomain h hU U' A ν = ⊤ := by
  apply (scalarDomain_eq_top_iff_integrable_at_one h hU U' A ν).mpr
  intro f ℓ
  obtain ⟨C, hC, hb⟩ := scalarIntegrand_bound h hU U' A K hK ξ hξ hcoeff f ℓ
  apply (hW.const_mul C).mono'
    (scalarIntegrand_aestronglyMeasurable h hU U' A ν 1 f ℓ)
  apply Filter.Eventually.of_forall
  intro q
  obtain ⟨u', hu', he⟩ := hfactor q
  have h1 := hb 1 u' (p q) (k q) (by rw [mul_one, he])
  rw [hu'] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (hle q) hC.le)

end Majorant

end StandardIntertwining

section QuotientDecay

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (U' : Subgroup G)

/-- **Locally uniform decay along chosen representatives.** For a choice `σ` of
representatives of the actual quotient `(U ∩ U') \ U'`, an envelope `ξ` on the Levi and a
function `W` on the quotient: near every `χ₀ ∈ Ω` there is one constant `C` such that for every
quotient point `q` and every factorization `σ q = p κ` with `p ∈ P`, `κ ∈ K`, the source half
modulus times `‖χ‖ ξ` at the Levi projection of `p` is at most `C * W q`. -/
def IsLocallyUniformQuotientDecayOn (σ : QuotientSpace (U := U) U' → U') (ξ : M → ℝ)
    (W : QuotientSpace (U := U) U' → ℝ) (Ω : Set (unramifiedCharacters ν)) : Prop :=
  ∀ χ₀ ∈ Ω, ∃ N ∈ 𝓝 χ₀, ∃ C : ℝ, ∀ χ ∈ N, ∀ (q : QuotientSpace (U := U) U') (p : P) (κ : K),
    ((σ q : U') : G) = (p : G) * (κ : G) →
    ‖(HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer (h.projection p) : ℂ)‖ *
        (‖(χ.val (h.projection p) : ℂ)‖ * ξ (h.projection p)) ≤ C * W q

variable (hδ : IsUnimodularModulus U hU) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

include hPK hK in
/-- **Full scalar convergence on the decay set.** If every coefficient of `A` is bounded by a
multiple of `ξ`, and the weights decay along representatives against an integrable `W` on `Ω`,
then every twist by a character of `Ω` has full scalar domain. -/
theorem scalarDomain_twist_eq_top_of_quotientDecay
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (σ : QuotientSpace (U := U) U' → U') (hσ : ∀ q, Quotient.mk _ (σ q) = q)
    (W : QuotientSpace (U := U) U' → ℝ) (hW : Integrable W qν)
    {Ω : Set (unramifiedCharacters ν)} (hdecay : IsLocallyUniformQuotientDecayOn h hU K ν U' σ ξ W Ω)
    (χ : unramifiedCharacters ν) (hχ : χ ∈ Ω) :
    scalarDomain h hU U' (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν =
      ⊤ := by
  choose p κ hpκ using fun q : QuotientSpace (U := U) U' => hPK ((σ q : U') : G)
  obtain ⟨N, hN, C, hC⟩ := hdecay χ hχ
  refine StandardIntertwining.scalarDomain_eq_top_of_le_integrable h hU U' qν _ K hK
    (fun m => ‖(χ.val m : ℂ)‖ * ξ m) (fun m => mul_nonneg (norm_nonneg _) (hξ m))
    (coefficientEnvelope_twist A χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) ξ hcoeff)
    p κ (fun q => ⟨σ q, hσ q, hpκ q⟩) (fun q => C * W q) (hW.const_mul C) (fun q => ?_)
  exact hC χ (mem_of_mem_nhds hN) q (p q) (κ q) (hpκ q)

omit [BorelSpace (QuotientSpace (U := U) U')] in
include hδ in
/-- **Local integrable domination on the decay set.** Under the coefficient bound and the
locally uniform decay against an integrable `W`, the actual compact integrands satisfy
`CompactIntegralLocallyDominatedOn` on `Ω`. -/
theorem compactIntegralLocallyDominatedOn_of_quotientDecay
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (σ : QuotientSpace (U := U) U' → U') (hσ : ∀ q, Quotient.mk _ (σ q) = q)
    (W : QuotientSpace (U := U) U' → ℝ) (hW : Integrable W qν)
    {Ω : Set (unramifiedCharacters ν)} (hdecay : IsLocallyUniformQuotientDecayOn h hU K ν U' σ ξ W Ω) :
    CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr A U' qν Ω := by
  intro f k ℓ χ₀
  -- Finitely many values of the compact section.
  let v : K → A := fun κ => eval _ _ f κ
  have hv : (Set.range v).Finite := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact (eval_isLocallyConstant _ _ f).range_finite
  choose c hcpos hc using fun w : A => hcoeff w ℓ
  obtain ⟨B, hB⟩ := (hv.image c).bddAbove
  let C₁ := max 1 B
  obtain ⟨N, hN, C, hC⟩ := hdecay χ₀.val χ₀.2
  refine ⟨fun q => C₁ * (C * W q), (hW.const_mul C).const_mul C₁, ?_⟩
  have hNΩ : ∀ᶠ χ : Ω in 𝓝 χ₀, (χ : unramifiedCharacters ν) ∈ N :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  filter_upwards [hNΩ] with χ hχN
  refine Filter.Eventually.of_forall fun q => ?_
  obtain ⟨p, κ, hpκ⟩ := hPK ((σ q : U') : G)
  have hval : unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f k χ.val q =
      (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
        ((χ.val.val (h.projection p) : ℂ) •
          A.representation (h.projection p) (v (κ * k))) := by
    conv_lhs => rw [← hσ q]
    change eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ.val
      A).symm f) (((σ q : U') : G) * (k : G)) = _
    rw [hpκ, mul_assoc, ← Subgroup.coe_mul, unramifiedLeviInductionCompactEquiv_symm_mul]
    rfl
  have hhalf : (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) =
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer (h.projection p) : ℂ) := by
    rw [closedHalfCharacter_eq_comp_projection h hU hδ]
    rfl
  have hcoef : ‖ℓ.val (A.representation (h.projection p) (v (κ * k)))‖ ≤
      C₁ * ξ (h.projection p) :=
    (hc (v (κ * k)) (h.projection p)).trans
      (mul_le_mul_of_nonneg_right
        ((hB ⟨v (κ * k), ⟨κ * k, rfl⟩, rfl⟩).trans (le_max_right 1 B))
        (hξ (h.projection p)))
  have hdec := hC χ.val hχN q p κ hpκ
  rw [hval, map_smul, map_smul, norm_smul, norm_smul, hhalf]
  calc ‖(HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer (h.projection p) : ℂ)‖ *
        (‖(χ.val.val (h.projection p) : ℂ)‖ *
          ‖ℓ.val (A.representation (h.projection p) (v (κ * k)))‖)
      ≤ ‖(HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer (h.projection p) : ℂ)‖ *
        (‖(χ.val.val (h.projection p) : ℂ)‖ * (C₁ * ξ (h.projection p))) := by
        gcongr
    _ = C₁ * (‖(HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
          (h.projection p) : ℂ)‖ *
        (‖(χ.val.val (h.projection p) : ℂ)‖ * ξ (h.projection p))) := by ring
    _ ≤ C₁ * (C * W q) :=
        mul_le_mul_of_nonneg_left hdec (zero_le_one.trans (le_max_left 1 B))

end QuotientDecay

end Langlands.Plancherel
