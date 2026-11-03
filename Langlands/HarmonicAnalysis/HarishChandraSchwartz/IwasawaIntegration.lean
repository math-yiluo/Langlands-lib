import Langlands.Analysis.Local.CompactFactorizationIntegral
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound

/-! # The integration formula `dg = δ_P(m)^{-1} du dm dk` (Waldspurger I.1 (2))

Waldspurger 2003, I.1 (2), first formula: for a semi-standard parabolic subgroup
`P = M U` and `f ∈ C_c^∞(G)`,
`∫_G f(g) dg = ∫_{U × M × K} f(u m k) δ_P(m)^{-1} dk dm du`, the Haar measures being
normalized by `mes(H ∩ K) = 1`. This module proves the formula for abstract data: a left
invariant measure on `G`, left invariant measures on `M` and `U` of mass one on `M ∩ K` and
`U ∩ K`, the factorization `G = M U K`, the decomposition `P ∩ K = (M ∩ K)(U ∩ K)` and the
modulus relation `IsConjModulus`. The proof applies the Library's factorization theorem
`CompactFactorization.lintegral_restrict_lintegral_mul` to the coordinates
`(m, u) ↦ m u` of `P`, in which left translations are skew products.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Measure

namespace Langlands.HarishChandraSchwartz

universe u

section Coordinates

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M U : Subgroup G} (hMU : M ≤ Subgroup.normalizer (U : Set G))

/-- The coordinates `(m, u) ↦ m u` of `P = M U`. -/
def leviUnipotentMul (x : M × U) : G :=
  (x.1 : G) * x.2

/-- Left translation by `(m₀ u₀)⁻¹` in the coordinates `(m, u)`:
`(m₀ u₀)⁻¹ m u = (m₀⁻¹ m) · ((m₀⁻¹ m)⁻¹ u₀⁻¹ (m₀⁻¹ m)) u`. -/
def leviUnipotentShift (x₀ : M × U) (x : M × U) : M × U :=
  (x₀.1⁻¹ * x.1, conjUnipotent hMU (x₀.1⁻¹ * x.1)⁻¹ x₀.2⁻¹ * x.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem leviUnipotentMul_shift (x₀ x : M × U) :
    leviUnipotentMul (leviUnipotentShift hMU x₀ x) =
      (leviUnipotentMul x₀)⁻¹ * leviUnipotentMul x := by
  simp only [leviUnipotentMul, leviUnipotentShift, conjUnipotent, Subgroup.coe_mul,
    InvMemClass.coe_inv]
  group

theorem continuous_leviUnipotentMul : Continuous (leviUnipotentMul (M := M) (U := U)) :=
  (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

theorem continuous_leviUnipotentShift_snd (x₀ : M × U) :
    Continuous (Function.uncurry fun (m : M) (u : U) =>
      conjUnipotent hMU (x₀.1⁻¹ * m)⁻¹ x₀.2⁻¹ * u) := by
  refine Continuous.subtype_mk ?_ _
  have hc : Continuous fun p : M × U => (((x₀.1⁻¹ * p.1)⁻¹ : M) : G) :=
    continuous_subtype_val.comp ((continuous_const.mul continuous_fst).inv)
  exact ((hc.mul continuous_const).mul hc.inv).mul (continuous_subtype_val.comp continuous_snd)

end Coordinates

section Integration

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {M U : Subgroup G} [SecondCountableTopology U]
  (hMU : M ≤ Subgroup.normalizer (U : Set G))
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant]
  {μU : Measure U} [SFinite μU] [μU.IsMulLeftInvariant]

omit [SecondCountableTopology G] in
include hMU in
/-- In the coordinates `(m, u)`, left translation by `(m₀ u₀)⁻¹` preserves `dm × du`:
it is the left translation by `m₀⁻¹` on `M` and, in each fiber, a left translation of `U`. -/
theorem measurePreserving_leviUnipotentShift (x₀ : M × U) :
    MeasurePreserving (leviUnipotentShift hMU x₀) (μM.prod μU) (μM.prod μU) :=
  (measurePreserving_mul_left μM x₀.1⁻¹).skew_product
    (continuous_leviUnipotentShift_snd hMU x₀).measurable
    (Filter.Eventually.of_forall fun _ => map_mul_left_eq_self _ _)

include hMU in
/-- Waldspurger I.1 (2), first formula, in the coordinates `p = m u`: if `G = M U K`,
`m u ∈ K ↔ m ∈ K ∧ u ∈ K`, and `μ_M`, `μ_U` give mass one to `M ∩ K`, `U ∩ K`, then
`∫_G F dμ = ∫_K ∫_M ∫_U F(m u k) du dm dk` for every measurable `F ≥ 0`, where `dk` is the
restriction of `μ` to `K`. -/
theorem lintegral_eq_lintegral_levi_unipotent {K : Subgroup G}
    (hK : MeasurableSet (K : Set G))
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hPK : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (hUK : μU {u : U | (u : G) ∈ K} = 1)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F g ∂μ = ∫⁻ k in (K : Set G), ∫⁻ m, ∫⁻ u, F ((m : G) * u * k) ∂μU ∂μM ∂μ := by
  have hι : Measurable (leviUnipotentMul (M := M) (U := U)) :=
    continuous_leviUnipotentMul.measurable
  have h := CompactFactorization.lintegral_restrict_lintegral_mul μ K hK (μM.prod μU)
    leviUnipotentMul hι
    (fun g => by
      obtain ⟨m, u, k, hk, rfl⟩ := hfac g
      exact ⟨(m, u), k, hk, rfl⟩)
    (fun x₀ => ⟨leviUnipotentShift hMU x₀, measurePreserving_leviUnipotentShift hMU x₀,
      fun x => leviUnipotentMul_shift hMU x₀ x⟩) F hF
  have hpre : leviUnipotentMul ⁻¹' (K : Set G) =
      {m : M | (m : G) ∈ K} ×ˢ {u : U | (u : G) ∈ K} := by
    ext x
    simp only [Set.mem_preimage, leviUnipotentMul, SetLike.mem_coe, Set.mem_prod,
      Set.mem_ofPred_eq]
    exact hPK x.1 x.2
  rw [hpre, Measure.prod_prod, hMK, hUK, one_mul, one_mul] at h
  rw [← h]
  refine lintegral_congr fun k => ?_
  have hm : Measurable fun x : M × U => F (leviUnipotentMul x * k) :=
    hF.comp (hι.mul_const k)
  rw [lintegral_prod _ hm.aemeasurable]
  rfl

include hMU in
/-- Waldspurger I.1 (2), first formula, in his order `u m k`: under the hypotheses of
`lintegral_eq_lintegral_levi_unipotent` and the modulus relation `IsConjModulus hMU μU δ`
(`μ_U(m S m⁻¹) = δ(m) μ_U(S)`),
`∫_G F dμ = ∫_K ∫_M δ(m)^{-1} ∫_U F(u m k) du dm dk`. -/
theorem lintegral_eq_lintegral_unipotent_levi {K : Subgroup G} {δ : M →* ℝ≥0ˣ}
    (hν : IsConjModulus hMU μU δ) (hK : MeasurableSet (K : Set G))
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hPK : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (hUK : μU {u : U | (u : G) ∈ K} = 1)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F g ∂μ = ∫⁻ k in (K : Set G), ∫⁻ m,
      (((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ u, F ((u : G) * m * k) ∂μU ∂μM ∂μ := by
  rw [lintegral_eq_lintegral_levi_unipotent hMU hK hfac hPK hMK hUK F hF]
  refine lintegral_congr fun k => lintegral_congr fun m => ?_
  have h := hν.lintegral_comp m (fun v : U => F ((v : G) * m * k))
  rw [← h]
  refine lintegral_congr fun u => ?_
  simp only [conjUnipotent]
  congr 1
  group

end Integration

end Langlands.HarishChandraSchwartz
