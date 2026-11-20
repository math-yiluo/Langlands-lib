import Langlands.Analysis.Local.QuotientWeilKernel
import Langlands.Analysis.Local.QuotientAutomorphismStatement

/-! # Haar change of variables for a twisted conjugation map -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

namespace Langlands.QuotientIntegration

universe u

/-- The displacement of a point by a group automorphism, in the order used by
conjugation of a Levi point by an element of a parabolic radical. -/
def twistedConjugationMap {G : Type u} [Group G] (α : G → G) (x : G) : G :=
  (α x)⁻¹ * x

section Conjugation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def conjugation (g : G) : G ≃ₜ* G where
  toMulEquiv := MulAut.conj g
  continuous_toFun := IsTopologicalGroup.continuous_conj g
  continuous_invFun := by
    change Continuous fun x => (MulAut.conj g).symm x
    simpa only [MulAut.conj_symm_apply, inv_inv] using
      IsTopologicalGroup.continuous_conj g⁻¹

variable (N : Subgroup G) [N.Normal]

private def subgroupConjugation (g : G) : N ≃ₜ* N :=
  subgroupAutomorphism N (conjugation g) fun x => by
    change g * x * g⁻¹ ∈ N ↔ x ∈ N
    have hg : g ∈ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.mp hg x).symm

/-- Conjugation by a point in a compact open subgroup preserves the Haar
measure of a closed normal subgroup. -/
private theorem map_subgroupConjugation_eq_self_of_compactOpen
    [MeasurableSpace N] [BorelSpace N] [LocallyCompactSpace N]
    (hN : IsClosed (N : Set G))
    (μN : Measure N) [μN.IsHaarMeasure] [μN.Regular]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {g : G} (hg : g ∈ K) : μN.map (subgroupConjugation N g) = μN := by
  let ι := subgroupConjugation N g
  have hι : Measurable (ι : N → N) := ι.continuous.measurable
  let B := OpenSubgroup.comap N.subtype continuous_subtype_val K
  have hB : IsCompact (B : Set N) := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hpre : ι ⁻¹' (B : Set N) = B := by
    ext x
    change g * (x : G) * g⁻¹ ∈ K ↔ (x : G) ∈ K
    exact (Subgroup.mem_normalizer_iff.mp (K.toSubgroup.le_normalizer hg) x).symm
  have hscale := mulEquivHaarChar_smul_map μN ι
  have hm := congrArg (fun ν : Measure N => ν (B : Set N)) hscale
  change ((mulEquivHaarChar ι : ℝ≥0∞) • μN.map ι) (B : Set N) = μN (B : Set N) at hm
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hι B.isOpen.measurableSet, hpre] at hm
  have h1 : mulEquivHaarChar ι = 1 := by
    exact_mod_cast (ENNReal.mul_eq_right (B.isOpen.measure_ne_zero μN ⟨1, B.one_mem⟩)
      hB.measure_ne_top).mp hm
  simpa only [h1, one_smul] using hscale

end Conjugation

section Factorization

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
  [MeasurableSpace N] [BorelSpace N] [LocallyCompactSpace N]
  [MeasurableSpace (LeftQuotient N)] [BorelSpace (LeftQuotient N)]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
  (μN : Measure N) [SFinite μN] [μN.IsHaarMeasure] [μN.Regular] [μN.IsMulRightInvariant]
  (ν : Measure (LeftQuotient N)) (hν : IsCompatible N μG μN ν)

include hN hν in
/-- If the displacement maps on a closed normal subgroup and on the quotient
scale the indicated measures, their product is the scale of the displacement
map on the group. A compact open cover ensures that the conjugation on each
normal fibre preserves its Haar measure. -/
theorem map_twistedConjugationMap_of_quotient
    (hcover : ∀ g : G, ∃ B : OpenSubgroup G, IsCompact (B : Set G) ∧ g ∈ B)
    (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ N ↔ x ∈ N)
    (τ : LeftQuotient N → LeftQuotient N) (hτ : Measurable τ)
    (hτ_mk : ∀ g, τ (leftQuotientMap N g) = leftQuotientMap N (twistedConjugationMap α g))
    (cN cQ : ℝ≥0∞)
    (hmapN : μN.map (twistedConjugationMap (subgroupAutomorphism N α hα)) = cN • μN)
    (hmapQ : ν.map τ = cQ • ν) :
    μG.map (twistedConjugationMap α) = (cN * cQ) • μG := by
  let L := twistedConjugationMap α
  let LN := twistedConjugationMap (subgroupAutomorphism N α hα)
  change μN.map LN = cN • μN at hmapN
  have hL : Measurable L := (α.continuous.inv.mul continuous_id).measurable
  have hLN : Measurable LN :=
    ((subgroupAutomorphism N α hα).continuous.inv.mul continuous_id).measurable
  let κ := orbitKernel N hN μN
  have hκ (q : LeftQuotient N) : (κ q).map L = cN • κ (τ q) := by
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    change (κ (leftQuotientMap N g)).map L = cN • κ (τ (leftQuotientMap N g))
    let ι := subgroupConjugation N (α g)⁻¹
    have hιm : Measurable (ι : N → N) := ι.continuous.measurable
    let e (n : N) : G := n.val * L g
    have he : Measurable e := (continuous_subtype_val.mul_const _).measurable
    have ht : Measurable fun n : N => n.val * g :=
      (continuous_subtype_val.mul_const _).measurable
    have hcomp : L ∘ (fun n : N => n.val * g) = e ∘ ι ∘ LN := by
      funext n
      change (α ((n : G) * g))⁻¹ * ((n : G) * g) =
        ((α g)⁻¹ * ((α (n : G))⁻¹ * (n : G)) * ((α g)⁻¹)⁻¹) * ((α g)⁻¹ * g)
      rw [map_mul]
      group
    obtain ⟨B, hB, hg⟩ := hcover (α g)⁻¹
    have hι := map_subgroupConjugation_eq_self_of_compactOpen N hN μN B hB hg
    change μN.map ι = μN at hι
    rw [hτ_mk]
    change (μN.map (fun n : N => n.val * g)).map L = cN • μN.map e
    rw [Measure.map_map hL ht, hcomp, ← Measure.map_map he (hιm.comp hLN),
      ← Measure.map_map hιm hLN, hmapN, Measure.map_smul _ hιm.aemeasurable, hι,
      Measure.map_smul _ he.aemeasurable]
  ext s hs
  have hμG : κ ∘ₘ ν = μG := orbitKernel_comp N hN μN μG ν hν
  have hmeas : Measurable fun q => κ q s := Measure.measurable_coe hs |>.comp κ.measurable
  rw [← hμG, Measure.map_apply hL hs, Measure.smul_apply, smul_eq_mul]
  change Measure.bind ν κ (L ⁻¹' s) = (cN * cQ) * Measure.bind ν κ s
  rw [Measure.bind_apply (hL hs) κ.measurable.aemeasurable,
    Measure.bind_apply hs κ.measurable.aemeasurable]
  calc
    _ = ∫⁻ q, (κ q).map L s ∂ν := by
      simp_rw [Measure.map_apply hL hs]
    _ = cN * ∫⁻ q, κ (τ q) s ∂ν := by
      simp_rw [hκ, Measure.smul_apply, smul_eq_mul]
      exact lintegral_const_mul _ (hmeas.comp hτ)
    _ = cN * ∫⁻ q, κ q s ∂ν.map τ := by rw [lintegral_map hmeas hτ]
    _ = _ := by rw [hmapQ, lintegral_smul_measure, smul_eq_mul, mul_assoc]

end Factorization

end Langlands.QuotientIntegration
