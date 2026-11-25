import Langlands.ClassFieldTheory.Local.QuadraticNormBall
import Langlands.HarmonicAnalysis.QuadraticExtensionTopology
import Langlands.HarmonicAnalysis.LinearHaarScaling
import Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral
import Langlands.Theta.WeilIndex.Defs

/-!
# The Gauss integral of the norm form

GKT chapter 3 for the norm form of a quadratic extension, in the language of Gauss integrals
(Definition 3.4, p. 76; Corollary 3.12, p. 80): `γ(ψ_t ∘ N) = η(t) γ(ψ ∘ N)`, which is Corollary
11.4 (p. 315) for the one-dimensional Hermitian space. Internal lemmas for the Leray splitting of
`U(ν, ν)`. For a quadratic extension `E / F` with norm `N` and a
non-trivial character `ψ` of `F`, the regularized integral of `z ↦ ψ(t N(z))` over `E`
(`HasGaussIntegral`) is `g · η(t) |t|⁻¹` with a constant `g` independent of `t`, `η` the quadratic
character of `E / F` (`hasGauss_norm_mul`). For `t` a norm this is the change of variables
`z ↦ w z`. For `t` not a norm, the measure `n₁ + n_t` on `F` with `n_a = |a| · (z ↦ a N(z))_* μ` is
homogeneous (multiplication by `u` permutes the classes of `Fˣ` modulo norms, because the norms have
index two), hence a multiple of Haar measure (`eq_smul_addHaar_of_map_mul_left`), and the integral
of `ψ` over a large ball vanishes (`gauss_cancel`). The integrals of a character of second degree
over large compact open subgroups are eventually constant (`gauss_integral_eventually_const`).

With the Weil index of `Langlands.Theta.WeilIndex.Defs` (the phase of the Gauss integral):
`z ↦ ψ(t N(z))` is a character of second degree (`isCharacterOfSecondDegree_mul_norm`) and
`γ(ψ ∘ t N) = η(t) γ(ψ ∘ N)` (`weilIndex_mul_norm`).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis
open LocalClassField (valuationBall isCompact_valuationBall isOpen_valuationBall normSign
  normSign_mul exists_addSubgroup_norm_mem_valuationBall exists_addSubgroup_norm_mem_valuationBall')

namespace Unitary.Internal

namespace Cancel

open ValuativeRel
open scoped Topology NNReal

theorem compact_subset_cball {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {K : Set F} (hK : IsCompact K) :
    ∃ s : Fˣ, K ⊆ valuationBall s := by
  refine hK.elim_directed_cover (fun s : Fˣ => valuationBall s) isOpen_valuationBall ?_ ?_
  · intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [valuationBall, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [valuationBall]⟩
  · intro a b
    rcases le_total (valuation F (a : F)) (valuation F (b : F)) with h | h
    · exact ⟨b, fun x hx => le_trans (show valuation F x ≤ _ from hx) h, fun x hx => hx⟩
    · exact ⟨a, fun x hx => hx, fun x hx => le_trans (show valuation F x ≤ _ from hx) h⟩

theorem punctured_neBot (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (𝓝[≠] (0 : F)).NeBot := by
  by_contra h
  rw [Filter.not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  obtain ⟨s, hs⟩ := exists_setOf_valuation_le_subset (h.mem_nhds rfl)
  exact s.ne_zero (hs (by simp))

theorem mul_mem_cball_iff {F : Type} [Field F] [ValuativeRel F] (a s : Fˣ) (x : F) :
    valuation F ((a : F) * x) ≤ valuation F (s : F) ↔ valuation F x ≤ valuation F
        ((a⁻¹ * s : Fˣ) : F) := by
  rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    le_inv_mul_iff₀ (by simp [zero_lt_iff])]

theorem gauss_cancel : ∀ (F : Type) [Field F] [NeZero (2 : F)] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (ψ : AddChar F ℂ)
    (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ,
    (s₀ : F) ∈ valuationBall s → (∫ z in {z : E | Algebra.norm F z ∈ valuationBall s},
    ψ (Algebra.norm F z) ∂μ) + (distribHaarChar F t : ℂ) * ∫ z in {z : E |
    (t : F) * Algebra.norm F z ∈ valuationBall s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _ t ht
  borelize F
  have hfd : FiniteDimensional F E := hE.finite
  have hring : IsTopologicalRing E := hE.isTopologicalRing
  have ht2 : T2Space E := hE.t2Space
  have hN : Continuous (Algebra.norm F : E → F) := hE.continuous_norm
  have : IsGalois F E := hE.isGalois
  have := punctured_neBot F
  have : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot F E 0
  have : LocallyCompactSpace E := by
    obtain ⟨L, -, h1, h2⟩ := exists_addSubgroup_norm_mem_valuationBall' hE 1
    exact h1.locallyCompactSpace_of_mem_nhds_of_addGroup (h2.mem_nhds L.zero_mem)
  have hμ0 : μ {0} = 0 := measure_singleton 0
  obtain ⟨lam, hlam⟩ : ∃ lam : Measure F, lam.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨s₀, hs₀⟩ := exists_setIntegral_setOf_valuation_le_eq_zero lam hψ0
  have hm : ∀ a : F, Measurable fun z : E => a * Algebra.norm F z := fun a =>
    (continuous_const.mul hN).measurable
  let m : Fˣ → Measure F := fun a => μ.map fun z : E => (a : F) * Algebra.norm F z
  let n : Fˣ → Measure F := fun a => distribHaarChar F a • m a
  have hmc : ∀ a, IsFiniteMeasureOnCompacts (m a) := fun a => ⟨fun K hK => by
    obtain ⟨s, hs⟩ := compact_subset_cball hK
    obtain ⟨L, hL, h1, -⟩ := exists_addSubgroup_norm_mem_valuationBall' hE (a⁻¹ * s)
    rw [Measure.map_apply (hm a) hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h1.measure_lt_top (μ := μ))
    intro z hz
    rw [hL]
    exact (mul_mem_cball_iff a s _).mp (hs hz)⟩
  have hnc : ∀ a, IsFiniteMeasureOnCompacts (n a) := fun a => by
    have := hmc a
    exact IsFiniteMeasureOnCompacts.smul_nnreal (m a) _
  have hn0 : ∀ a, n a {0} = 0 := fun a => by
    have : (fun z : E => (a : F) * Algebra.norm F z) ⁻¹' {0} = {0} := by
      ext z; simp [Algebra.norm_eq_zero_iff]
    simp only [n, m, Measure.smul_apply]
    rw [Measure.map_apply (hm a) (measurableSet_singleton 0), this, hμ0, smul_zero]
  have hn1 : ∀ (a : Fˣ) (b : Fˣ),
      b ∈ (Units.map (Algebra.norm F : E →* F)).range → n (b * a) = n a := by
    rintro a _ ⟨w, rfl⟩
    have h1 := map_mul_left_addHaar_algebra (F := F) μ w
    have h2 : m (Units.map (Algebra.norm F : E →* F) w * a) =
        (μ.map fun x => (w : E) * x).map fun z : E => (a : F) * Algebra.norm F z := by
      rw [Measure.map_map (hm a) (measurable_const_mul _)]
      simp only [m]
      congr 1
      funext z
      simp only [Units.val_mul, Units.coe_map, Function.comp, map_mul]
      ring
    simp only [n]
    rw [h2, h1, Measure.map_smul, smul_smul, map_mul, mul_right_comm,
      mul_inv_cancel₀ (distribHaarChar_pos).ne', one_mul]
    exact (hm a).aemeasurable
  have hn2 : ∀ a u : Fˣ,
      (n a).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n (u * a) := by
    intro a u
    simp only [n, m]
    rw [Measure.map_smul, Measure.map_map (measurable_const_mul _) (hm a), smul_smul, map_mul,
      inv_mul_cancel_left₀ (distribHaarChar_pos).ne']
    · congr 2
      funext z
      simp [mul_assoc]
    · exact (measurable_const_mul _).aemeasurable
  have hhom : ∀ u : Fˣ,
      (n 1 + n t).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • (n 1 + n t) := by
    intro u
    rw [Measure.map_add _ _ (measurable_const_mul _), hn2, hn2, ← smul_add]
    congr 1
    by_cases hu : u ∈ (Units.map (Algebra.norm F : E →* F)).range
    · rw [hn1 _ _ hu, hn1 _ _ hu]
    · have h1 := LocalClassField.mul_mem_range_norm_of_finrank_eq_two hE.finrank_eq_two hu ht
      have h2 := LocalClassField.mul_mem_range_norm_of_finrank_eq_two hE.finrank_eq_two ht ht
      have h3 := hn1 1 _ h1
      have h4 := hn1 t _ (mul_mem h1 (inv_mem h2))
      rw [mul_one] at h3
      have h5 : u * t * (t * t)⁻¹ * t = u * 1 := by group
      rw [h5] at h4
      rw [h3, h4, add_comm]
  have := hnc 1
  have := hnc t
  have : IsFiniteMeasureOnCompacts (n 1 + n t) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  obtain ⟨r, hr⟩ := eq_smul_addHaar_of_map_mul_left lam (n 1 + n t) (by rw [Measure.add_apply, hn0,
      hn0, add_zero]) hhom
  refine ⟨s₀, fun s hs => ?_⟩
  have hB := isCompact_valuationBall s
  have hint : ∀ a : Fˣ, ∫ x in valuationBall s, ψ x ∂(n a) = (distribHaarChar F a : ℂ) *
      ∫ z in {z : E | (a : F) * Algebra.norm F z ∈ valuationBall s}, ψ ((a : F) * Algebra.norm F z) ∂μ := by
    intro a
    simp only [n, m]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      setIntegral_map hB.measurableSet hψ.aestronglyMeasurable (hm a).aemeasurable]
    rfl
  have h1 : ∫ x in valuationBall s, ψ x ∂(n 1 + n t) = 0 := by
    rw [hr, Measure.restrict_smul, integral_smul_nnreal_measure, hs₀ s hs, smul_zero]
  rw [Measure.restrict_add, integral_add_measure (hψ.continuousOn.integrableOn_compact hB)
    (hψ.continuousOn.integrableOn_compact hB), hint, hint] at h1
  simpa [map_one] using h1

end Cancel


theorem setIntegral_addSubgroup_add {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] (H : AddSubgroup X)
    (hH : MeasurableSet (H : Set X)) {h : X} (hh : h ∈ H) (g : X → ℂ) :
    ∫ x in (H : Set X), g (x + h) ∂μ = ∫ x in (H : Set X), g x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have key : (Set.indicator (H : Set X) fun x => g (x + h)) =
      fun x => Set.indicator (H : Set X) g (x + h) := by
    funext x
    by_cases hx : x ∈ H
    · have hx' : x + h ∈ H := H.add_mem hx hh
      simp [hx, hx']
    · have hx' : x + h ∉ H := fun h' => hx (by simpa using H.sub_mem h' hh)
      simp [hx, hx']
  rw [key, integral_add_right_eq_self (Set.indicator (H : Set X) g) h]

open Classical in
theorem setIntegral_pair_char {X : Type} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] {e : X → X → ℂ}
        (he : IsSelfDualBicharacter e)
    (M : AddSubgroup X) (hM : MeasurableSet (M : Set X)) (x : X) :
    ∫ m in (M : Set X), e x m ∂μ =
      if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0 := by
  split_ifs with hx
  · rw [setIntegral_congr_fun hM (g := fun _ => (1 : ℂ)) (fun m hm => by
      simp only; rw [he.symm]; exact hx m hm)]
    rw [setIntegral_const]
    simp
  · push Not at hx
    obtain ⟨m₀, hm₀, hne⟩ := hx
    have h := setIntegral_addSubgroup_add μ M hM hm₀ (fun m => e x m)
    have hsplit : ∀ m, e x (m + m₀) = e x m * e x m₀ := fun m => by
      rw [he.symm x, he.map_add_left, he.symm m, he.symm m₀]
    simp only [hsplit] at h
    rw [integral_mul_const] at h
    have hne' : e x m₀ ≠ 1 := by rwa [he.symm]
    have h2 : (∫ m in (M : Set X), e x m ∂μ) * (e x m₀ - 1) = 0 := by
      rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne'

open Classical in
theorem gauss_integral_eventually_const : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X]
    [MeasurableSpace X]
    [BorelSpace X] [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [CompactOpenExhaustion X] (μ : Measure X) [μ.IsAddHaarMeasure]
    (e : X → X → ℂ),
        IsSelfDualBicharacter e →
    ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) →
    ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X,
        IsCompact (L : Set X) → IsOpen (L : Set X) →
      K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  intro X _ _ _ _ _ _ _ _ _ μ _ e he f hf hf0 hfe
  obtain ⟨M, hMc, hMo, hMf⟩ := CompactOpenExhaustion.exists_subset {x | f x = 1} ((hf.isOpen_fiber 1).mem_nhds hf0)
  have hMn : (M : Set X) ∈ 𝓝 (0 : X) := hMo.mem_nhds M.zero_mem
  obtain ⟨K₀, hK₀c, hK₀⟩ := he.big _ hMn
  have hecont : ∀ m, Continuous (fun y => e m y) := fun m =>
    (he.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_id)).continuous
  set M' : Set X := {y | ∀ m ∈ (M : Set X), e m y = 1} with hM'
  have hM'cl : IsClosed M' := by
    have : M' = ⋂ m ∈ (M : Set X), {y | e m y = 1} := by ext; simp [M']
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_eq (hecont m) continuous_const
  refine ⟨∫ x in M', f x ∂μ, (M : Set X) ∪ K₀, hMc.union hK₀c, ?_⟩
  intro L hLc hLo hKL
  have hML : (M : Set X) ⊆ L := Set.subset_union_left.trans hKL
  have hM'L : M' ⊆ L := fun y hy => hKL (Or.inr (hK₀ y hy))
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hMm : MeasurableSet (M : Set X) := hMo.measurableSet
  have hM'm : MeasurableSet M' := hM'cl.measurableSet
  have : IsFiniteMeasure (μ.restrict
      (L : Set X)) := isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  have : IsFiniteMeasure (μ.restrict
      (M : Set X)) := isFiniteMeasure_restrict.mpr hMc.measure_lt_top.ne
  set A := ∫ x in (L : Set X), f x ∂μ with hA
  have h1 : ∀ m ∈ (M : Set X), ∫ x in (L : Set X), f x * e x m ∂μ = A := by
    intro m hm
    rw [hA, ← setIntegral_addSubgroup_add μ L hLm (hML hm) f]
    congr 1; funext x
    rw [hfe, show f m = 1 from hMf hm]; ring
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hint : Integrable (Function.uncurry fun m x => f x * e x m)
      ((μ.restrict (M : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.isLocallyConstant.continuous.comp
            (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hMm.prod hLm) fun p hp => ?_
      show ‖f p.2 * e p.2 p.1‖ ≤ C
      rw [norm_mul, he.norm_eq_one, mul_one]
      exact hC p.2 hp.2
  have h3 := integral_integral_swap hint
  rw [setIntegral_congr_fun hMm h1, setIntegral_const] at h3
  simp_rw [integral_const_mul, setIntegral_pair_char μ he M hMm] at h3
  have h4 : ∫ x in (L : Set X), f x * (if ∀ m ∈ (M : Set X),
      e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0) ∂μ
      = ((μ.real (M : Set X) : ℝ) : ℂ) * ∫ x in M', f x ∂μ := by
    have : (fun x => f x * (if ∀ m ∈ (M : Set X),
        e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0)) =
        Set.indicator M' (fun x => ((μ.real (M : Set X) : ℝ) : ℂ) * f x) := by
      funext x
      by_cases hx : x ∈ M'
      · rw [Set.indicator_of_mem hx, ite_eq_left (show ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
      · rw [Set.indicator_of_notMem hx, ite_eq_right (show ¬ ∀ m ∈ (M : Set X),
          e m x = 1 from hx)]; ring
    rw [this, integral_indicator hM'm, Measure.restrict_restrict hM'm, Set.inter_eq_left.mpr hM'L,
      integral_const_mul]
  rw [h4, Complex.real_smul] at h3
  have hpos : ((μ.real (M : Set X) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne',
        hMc.measure_lt_top.ne⟩
  exact mul_left_cancel₀ hpos h3



namespace GaussNorm


section Ball

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem exists_cball_sup (a b : Fˣ) : ∃ s : Fˣ, valuationBall a ⊆ valuationBall s ∧ valuationBall b ⊆ valuationBall s := by
  rcases le_total (ValuativeRel.valuation F (a : F)) (ValuativeRel.valuation F (b : F)) with h | h
  · exact ⟨b,
      fun x (hx : ValuativeRel.valuation F x ≤ _) =>
      (le_trans hx h : ValuativeRel.valuation F x ≤ _),
      Set.Subset.rfl⟩
  · exact ⟨a, Set.Subset.rfl,
      fun x (hx : ValuativeRel.valuation F x ≤ _) =>
          (le_trans hx h : ValuativeRel.valuation F x ≤ _)⟩

theorem exists_cball_of_isCompact {K : Set F} (hK : IsCompact K) : ∃ s : Fˣ, K ⊆ valuationBall s := by
  have hcov : K ⊆ ⋃ s : Fˣ, valuationBall s := by
    intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [valuationBall, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [valuationBall]⟩
  have hd : Directed (· ⊆ ·) (fun s : Fˣ => valuationBall s) := by
    intro a b
    obtain ⟨s, h1, h2⟩ := exists_cball_sup a b
    exact ⟨s, h1, h2⟩
  exact hK.elim_directed_cover _ (fun s => isOpen_valuationBall s) hcov hd

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mul_mem_cball_iff (t s : Fˣ) (x : F) : (t : F) * x ∈ valuationBall s ↔ x ∈ valuationBall (t⁻¹ * s) := by
  simp only [valuationBall, Set.mem_ofPred_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [le_inv_mul_iff₀ (by simp [zero_lt_iff])]

end Ball

section Polar

variable {F : Type} [Field F] [NeZero (2 : F)] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E}
    {δ : E}

theorem algebraMap_norm_add (hE : IsQuadraticInvolution c δ) (x y : E) :
    algebraMap F E (Algebra.norm F
        (x + y) - Algebra.norm F x - Algebra.norm F y) = x * c y + y * c x := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  rw [map_sub, map_sub, hE.algebraMap_norm, hE.algebraMap_norm, hE.algebraMap_norm, map_add]
  ring

def polar (hE : IsQuadraticInvolution c δ) : E →ₗ[F] E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y)
    (fun x x' y => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (a • x + y) - Algebra.norm F (a • x) - Algebra.norm F y) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def,
          map_mul,
        AlgHom.commutes]; ring))
    (fun x y y' => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (x + a • y) - Algebra.norm F x - Algebra.norm F (a • y)) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def,
          map_mul,
        AlgHom.commutes]; ring))

theorem polar_apply (hE : IsQuadraticInvolution c δ) (x y : E) :
    polar hE x y = Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y := rfl

theorem algebraMap_polar (hE : IsQuadraticInvolution c δ) (x y : E) : algebraMap F E
    (polar hE x y) = x * c y + y * c x :=
  algebraMap_norm_add hE x y

theorem polar_symm (hE : IsQuadraticInvolution c δ) (x y : E) : polar hE x y = polar hE y x := by
  rw [polar_apply, polar_apply, add_comm x y]; ring

theorem polar_nondeg (hE : IsQuadraticInvolution c δ) (y : E) (hy : ∀ x,
    polar hE x y = 0) : y = 0 := by
  have h1 := congrArg (algebraMap F E) (hy y)
  rw [algebraMap_polar, map_zero] at h1
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]; exact (map_ne_zero _).mpr two_ne_zero
  have h3 : (2 : E) * (y * c y) = 0 := by rw [two_mul]; exact h1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2) with h | h
  · exact h
  · rw [← hE.involutive y, h, map_zero]

theorem polar_half (hE : IsQuadraticInvolution c δ) (z : E) : polar hE
    ((2 : F)⁻¹ • z) z = Algebra.norm F z := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  apply hE.algebraMap_injective
  rw [algebraMap_polar, hE.algebraMap_norm, Algebra.smul_def, map_mul, AlgHom.commutes]
  have h2 : algebraMap F E (2 : F)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  linear_combination (z * c z) * h2

theorem norm_add_eq (hE : IsQuadraticInvolution c δ) (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + polar hE x y := by
  rw [polar_apply]; ring

end Polar

end GaussNorm

open GaussNorm



theorem hasGauss_norm_mul : ∀ (F : Type) [Field F] [NeZero (2 : F)] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure],
    ∃ g : ℂ, ∀ t : Fˣ,
    HasGaussIntegral μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (normSign E t *
    ((distribHaarChar F t)⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _
  have hfin : FiniteDimensional F E := hE.finite
  have htr : IsTopologicalRing E := hE.isTopologicalRing
  have hNc : Continuous (Algebra.norm F : E → F) := hE.continuous_norm
  have := hfin
  have := htr
  have := IsModuleTopology.isTopologicalAddGroup F E
  have := t2Space_of_finiteDimensional F E
  have := locallyCompactSpace_of_finiteDimensional F E
  have := secondCountableTopology_of_finiteDimensional F E
  have := compactOpenExhaustion_of_finiteDimensional F E
  have hpair : IsSelfDualBicharacter fun x y => ψ (polar hE x y) :=
    isSelfDualBicharacter_of_symm hψ hψ1 hψ0 (polar hE) (polar_symm hE) (polar_nondeg hE)
  set f : E → ℂ := fun z => ψ (Algebra.norm F z) with hf
  have hlc : IsLocallyConstant f := by
    have h := hpair.isLocallyConstant.comp_continuous (show Continuous fun z : E => ((2 : F)⁻¹ • z,
        z) by fun_prop)
    have heq : ((fun p : E × E => ψ (polar hE p.1 p.2)) ∘ fun z : E => ((2 : F)⁻¹ • z, z)) = f := by
      funext z; simp only [Function.comp_apply, f, polar_half]
    rwa [heq] at h
  have hf0 : f 0 = 1 := by simp [f]
  have hfadd : ∀ x y, f (x + y) = f x * f y * ψ (polar hE x y) := by
    intro x y
    simp only [f]
    rw [norm_add_eq hE, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  obtain ⟨γ, K₁, hK₁, hγ⟩ := gauss_integral_eventually_const E μ _ hpair f hlc hf0 hfadd
  have hG : HasGaussIntegral μ f γ := by
    intro K hK
    obtain ⟨L, hLc, hLo, hL⟩ := CompactOpenExhaustion.exists_superset (K ∪ K₁) (hK.union hK₁)
    exact ⟨L, hLc, hLo, Set.subset_union_left.trans hL,
        hγ L hLc hLo (Set.subset_union_right.trans hL)⟩
  refine ⟨γ, fun t => ?_⟩
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · obtain ⟨w, hw⟩ := ht
    let T : E ≃ₜ+ E :=
      { toFun := fun z => (w : E) * z
        invFun := fun z => ((w⁻¹ : Eˣ) : E) * z
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        map_add' := fun x y => mul_add _ _ _
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have hT : μ.map T = (distribHaarChar F t)⁻¹ • μ := by
      have h := map_mul_left_addHaar_algebra (F := F) μ w
      rw [hw] at h
      exact h
    have h := HasGaussIntegral.comp_addEquiv T hT hG
    have e1 : (fun z : E => ψ ((t : F) * Algebra.norm F z)) = fun x => f (T x) := by
      funext z
      show ψ ((t : F) * Algebra.norm F z) = ψ (Algebra.norm F ((w : E) * z))
      rw [MonoidHom.map_mul (Algebra.norm F) (w : E) z, ← hw, Units.coe_map]
    have hs : normSign E t = 1 := by rw [normSign, ite_eq_left ⟨w, hw⟩]
    have e2 : γ * (normSign E t * (((distribHaarChar F t)⁻¹ : ℝ) : ℂ)) =
        (((((distribHaarChar F t)⁻¹ : NNReal) : ℝ)) : ℂ) * γ := by
      rw [hs, one_mul, mul_comm]
      simp [distribHaarChar]
    rw [e1, e2]
    exact h
  · obtain ⟨s₀, hcan⟩ := Cancel.gauss_cancel F E c δ hE ψ hψ hψ1 hψ0 μ t ht
    have hs : normSign E t = -1 := by rw [normSign, ite_eq_right ht]
    intro K hK
    obtain ⟨a₁, ha₁⟩ := exists_cball_of_isCompact (hK.image hNc)
    obtain ⟨a₂, ha₂⟩ := exists_cball_of_isCompact (hK₁.image hNc)
    obtain ⟨s', hs'1, hs'2⟩ := exists_cball_sup (t * a₁) a₂
    obtain ⟨s, hs1, hs2⟩ := exists_cball_sup s' s₀
    obtain ⟨L, hLeq, hLc, hLo⟩ := exists_addSubgroup_norm_mem_valuationBall' hE (t⁻¹ * s)
    obtain ⟨L₁, hL₁eq, hL₁c, hL₁o⟩ := exists_addSubgroup_norm_mem_valuationBall' hE s
    have hset : {z : E | (t : F) * Algebra.norm F z ∈ valuationBall s} = (L : Set E) := by
      rw [hLeq]; ext z; exact mul_mem_cball_iff t s _
    have hK₁L₁ : K₁ ⊆ L₁ := by
      intro z hz
      rw [hL₁eq]
      exact hs1 (hs'2 (ha₂ ⟨z, hz, rfl⟩))
    have hKL : K ⊆ L := by
      intro z hz
      rw [← hset]
      have h1 : Algebra.norm F z ∈ valuationBall a₁ := ha₁ ⟨z, hz, rfl⟩
      have h2 : (t : F) * Algebra.norm F z ∈ valuationBall (t * a₁) := by
        rw [mul_mem_cball_iff, inv_mul_cancel_left]; exact h1
      exact hs1 (hs'1 h2)
    have hs₀ : (s₀ : F) ∈ valuationBall s := hs2 (show ValuativeRel.valuation F
        (s₀ : F) ≤ ValuativeRel.valuation F (s₀ : F) from le_refl _)
    have h1 := hcan s hs₀
    rw [← hL₁eq, hγ L₁ hL₁c hL₁o hK₁L₁, hset] at h1
    refine ⟨L, hLc, hLo, hKL, ?_⟩
    have hn : (distribHaarChar F t : ℂ) ≠ 0 := by
        exact_mod_cast (distribHaarChar_pos (A := F) (g := t)).ne'
    rw [hs, Complex.ofReal_inv]
    field_simp
    linear_combination h1


end Unitary.Internal

/-! ### The norm form and the Weil index -/

section WeilIndex

open Unitary.Internal Unitary.Internal.GaussNorm

variable {F : Type} [Field F] [NeZero (2 : F)] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsModuleTopology F E] {c : E →ₐ[F] E} {δ : E} {ψ : AddChar F ℂ}

/-- `z ↦ ψ(t N_{E/F}(z))` is a character of second degree on `E` (GKT 3.1.3 for the norm form
`t N_{E/F}`, whose polar form `t tr_{E/F}(x c(y))` is non-degenerate). -/
theorem isCharacterOfSecondDegree_mul_norm (hE : IsQuadraticInvolution c δ) (hψ : Continuous ψ)
    (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) (t : Fˣ) :
    IsCharacterOfSecondDegree fun z : E => ψ ((t : F) * Algebra.norm F z) := by
  have : FiniteDimensional F E := hE.finite
  let β : E →ₗ[F] E →ₗ[F] F := (t : F) • polar hE
  have hβ : ∀ x y, β x y = (t : F) * polar hE x y := fun x y => rfl
  have he := HarmonicAnalysis.isSelfDualBicharacter_of_symm hψ hn h1 β
    (fun x y => by rw [hβ, hβ, polar_symm]) fun y hy => polar_nondeg hE y fun x => by
      have := hy x
      rw [hβ] at this
      exact (mul_eq_zero.mp this).resolve_left t.ne_zero
  refine IsCharacterOfSecondDegree.of_bicharacter he (fun z => hn _)
    ((HarmonicAnalysis.isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous
      (continuous_const.mul hE.continuous_norm)) fun x y => ?_
  rw [hβ, norm_add_eq hE, mul_add, mul_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

/-- **The Weil index of `t N_{E/F}`** (GKT Corollary 11.4 for the one-dimensional Hermitian space
`V = ⟨1⟩`, Proposition 3.30 for the norm form): `γ(ψ ∘ t N) = η(t) γ(ψ ∘ N)`, `η = normSign E`
the quadratic character of `E / F`. From the Gauss integrals `g η(t) |t|⁻¹` of
`hasGauss_norm_mul`. -/
theorem weilIndex_mul_norm (hE : IsQuadraticInvolution c δ) (hψ : Continuous ψ)
    (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) (t : Fˣ) :
    weilIndex (fun z : E => ψ ((t : F) * Algebra.norm F z)) =
      LocalClassField.normSign E t * weilIndex (fun z : E => ψ (Algebra.norm F z)) := by
  have : FiniteDimensional F E := hE.finite
  have := IsModuleTopology.isTopologicalAddGroup F E
  have := HarmonicAnalysis.locallyCompactSpace_of_finiteDimensional F E
  have := HarmonicAnalysis.secondCountableTopology_of_finiteDimensional F E
  have := HarmonicAnalysis.compactOpenExhaustion_of_finiteDimensional F E
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  obtain ⟨g, hg⟩ := hasGauss_norm_mul F E c δ hE ψ hψ hn h1 μ
  have hf : ∀ s : Fˣ, IsCharacterOfSecondDegree fun z : E => ψ ((s : F) * Algebra.norm F z) :=
    isCharacterOfSecondDegree_mul_norm hE hψ hn h1
  have h1' : (fun z : E => ψ (((1 : Fˣ) : F) * Algebra.norm F z)) =
      fun z : E => ψ (Algebra.norm F z) := by
    funext z; rw [Units.val_one, one_mul]
  have hs1 : LocalClassField.normSign E (1 : Fˣ) = 1 := by
    unfold LocalClassField.normSign; exact ite_eq_left (one_mem _)
  have hns : ‖LocalClassField.normSign E t‖ = 1 := by
    unfold LocalClassField.normSign; split_ifs <;> simp
  have hg1 := hg 1
  simp only [hs1, map_one, NNReal.coe_one, inv_one, Complex.ofReal_one, mul_one] at hg1
  have hg0 : g ≠ 0 := (hf 1).hasGaussIntegral_ne_zero μ hg1
  have hw1 := weilIndex_eq_div_norm (hf 1) μ hg1
  rw [h1'] at hw1
  rw [weilIndex_eq_div_norm (hf t) μ (hg t), hw1]
  have hr : (0 : ℝ) < ((distribHaarChar F t : NNReal) : ℝ)⁻¹ :=
    inv_pos.2 (by exact_mod_cast distribHaarChar_pos (A := F) (g := t))
  rw [norm_mul, norm_mul, hns, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hgn : (‖g‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hg0).ne'
  have hrc : ((((distribHaarChar F t : NNReal) : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hd : (((distribHaarChar F t : NNReal) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := F) (g := t)).ne'
  push_cast
  field_simp

end WeilIndex

end Langlands.Theta
