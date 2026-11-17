import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralKernelPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralFiniteReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralProjection
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction

/-! # The local kernel step of Waldspurger VIII.4.1 from central and `L²` weights

The kernel step `IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan` of
`RationalCuspidalCentralKernelStep` bounds the triple integral of VIII.4.1 with the convolution
weights of Lemma III.6.1. This module bounds it with the central weights and the `L²` weights
alone, by the Cauchy–Schwarz inequality on `A \ G`. The local step then needs no convolution
weights. It is combined with the diagonal reduction of `RationalCuspidalCentralKernelDiagonal`
and `RationalCuspidalCentralKernelPairing`.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate ENNReal

namespace Langlands.HarishChandraSchwartz

universe u uG

/-- `a b ≤ a² + b²` in `ℝ≥0∞`. -/
theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

section AbsIntegral

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Subgroup G} [MeasurableSpace A] {μA : Measure A} {Ξ σ : G → ℝ}

/-- If `f` lies in the level `C_H` of an open compact `H`, then
`Φ(g) = ∫_A |f(a g)| dμ_A(a)` is continuous: it is right `H`-invariant. -/
theorem continuous_centralAbsIntegral {H : CompactOpenSubgroup G} {f : G → ℂ}
    (hf : f ∈ levelSubmodule Ξ σ H.toSubgroup) : Continuous (centralAbsIntegral μA f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : {y : G | x⁻¹ * y ∈ (H.toSubgroup : Set G)} ∈ nhds x :=
    (H.1.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp)
  refine (continuousAt_const (y := centralAbsIntegral μA f x)).congr ?_
  filter_upwards [hn] with y hy
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ H.toSubgroup, y = x * k := ⟨x⁻¹ * y, hy, by group⟩
  unfold centralAbsIntegral
  refine lintegral_congr fun a => ?_
  have h := hf.1 1 H.toSubgroup.one_mem k hk ((a : G) * x)
  rw [one_mul] at h
  rw [← mul_assoc, h]

end AbsIntegral

section SquareBound

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}
  {Ξ σ : G → ℝ}

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace (LeftQuotient A)]
  [BorelSpace (LeftQuotient A)] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  [IsFiniteMeasureOnCompacts μG] in
/-- `Φ(g) = ∫_A |f(a g)| dμ_A(a)` is measurable for measurable `f`. -/
theorem measurable_centralAbsIntegral {f : G → ℂ} (hfm : Measurable f) :
    Measurable (centralAbsIntegral μA f) := by
  have h : Measurable fun p : G × A => ‖f ((p.2 : G) * p.1)‖ₑ :=
    (hfm.comp ((continuous_subtype_val.comp continuous_snd).mul
      continuous_fst).measurable).enorm
  exact h.lintegral_prod_right'

include hA in
/-- **`Φ` is square integrable on `A \ G`**: for measurable `f` with all `ν_r(f)` finite,
`∫_{A\G} Φ(q̇)² dν(q) < ∞`, where `Φ(g) = ∫_A |f(a g)| dμ_A(a)`. The proof is that of the
Library's `lintegral_enorm_centralProjection_out_sq_lt_top`: the Weil formula gives
`∫_{A\G} Φ² = ∫_G |f| Φ`, which is finite by the central and `L²` weights. -/
theorem lintegral_centralAbsIntegral_out_sq_lt_top [MeasurableMul A]
    (hν : IsCompatible A μG μA ν) (hw : CentralWeights μA Ξ σ) (hL : L2Weights μG Ξ σ)
    {f : G → ℂ} (hfm : Measurable f) (hf : ∀ r, nu Ξ σ r f < ⊤) :
    ∫⁻ q, centralAbsIntegral μA f q.out ^ 2 ∂ν < ⊤ := by
  obtain ⟨s, hs, hI⟩ := hw.exists_lintegral_lt_top
  obtain ⟨d, hd⟩ := hL.square
  set I := ∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA with hIdef
  set C := nu Ξ σ (s + d) f * nu Ξ σ s f * I with hCdef
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (hf _).ne (hf _).ne) hI.ne
  have hfA : ∀ g : G, Measurable fun a : A => ‖f ((a : G) * g)‖ₑ := fun g =>
    (hfm.comp (continuous_subtype_val.mul continuous_const).measurable).enorm
  have hΦm : Measurable (centralAbsIntegral μA f) := measurable_centralAbsIntegral hfm
  have hpt : ∀ g : G, ‖f g‖ₑ * centralAbsIntegral μA f g ≤
      C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) := by
    intro g
    have hb : 0 < 1 + σ g := by linarith [hw.nonneg g]
    have h1 : ‖f g‖ₑ ≤ nu Ξ σ (s + d) f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(s + d))) := by
      have h := norm_le_of_nu hw.pos hw.nonneg (hf (s + d)).ne g
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal (hf (s + d)).ne,
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal h
    have h2 := hw.lintegral_enorm_le hs (hf s).ne g
    have hx : 0 ≤ Ξ g * (1 + σ g) ^ (-(s + d)) :=
      mul_nonneg (hw.pos g).le (Real.rpow_nonneg hb.le _)
    have hreal : Ξ g * (1 + σ g) ^ (-(s + d)) * (Ξ g * (1 + σ g) ^ s) =
        Ξ g ^ 2 * (1 + σ g) ^ (-d) := by
      rw [show Ξ g * (1 + σ g) ^ (-(s + d)) * (Ξ g * (1 + σ g) ^ s) =
          Ξ g ^ 2 * ((1 + σ g) ^ (-(s + d)) * (1 + σ g) ^ s) by ring, ← Real.rpow_add hb]
      congr 2
      ring
    calc ‖f g‖ₑ * centralAbsIntegral μA f g
        ≤ (nu Ξ σ (s + d) f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(s + d)))) *
            (nu Ξ σ s f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) * I) := mul_le_mul' h1 h2
      _ = C * (ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(s + d))) *
            ENNReal.ofReal (Ξ g * (1 + σ g) ^ s)) := by rw [hCdef]; ring
      _ = C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) := by
          rw [← ENNReal.ofReal_mul hx, hreal]
  calc ∫⁻ q, centralAbsIntegral μA f q.out ^ 2 ∂ν
      = ∫⁻ q, ∫⁻ a, (fun g => ‖f g‖ₑ * centralAbsIntegral μA f g) ((a : G) * q.out) ∂μA ∂ν := by
        refine lintegral_congr fun q => ?_
        simp only [centralAbsIntegral_mul_left]
        rw [lintegral_mul_const _ (hfA q.out), sq]
        rfl
    _ = ∫⁻ g, ‖f g‖ₑ * centralAbsIntegral μA f g ∂μG :=
        lintegral_lintegral_out_eq hA hν (hfm.enorm.mul hΦm)
    _ ≤ ∫⁻ g, C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) ∂μG := lintegral_mono hpt
    _ = C * ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) ∂μG := lintegral_const_mul' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hd

include hA in
/-- **The Cauchy–Schwarz bound on `A \ G`.** For `φ, f` in the Schwartz space,
`∫_G |φ(x)| Φ_f(x) dμ_G(x) < ∞`, where `Φ_f(x) = ∫_A |f(a x)| dμ_A(a)`. By the Weil formula the
integral is `∫_{A\G} Φ_φ Φ_f`, which is at most `∫_{A\G} Φ_φ² + ∫_{A\G} Φ_f²`. -/
theorem lintegral_enorm_mul_centralAbsIntegral_lt_top [MeasurableMul A]
    [Nonempty (CompactOpenSubgroup G)] (hν : IsCompatible A μG μA ν)
    (hw : CentralWeights μA Ξ σ) (hL : L2Weights μG Ξ σ) {φ f : G → ℂ}
    (hφ : φ ∈ schwartzSubmodule Ξ σ) (hf : f ∈ schwartzSubmodule Ξ σ) :
    ∫⁻ x, ‖φ x‖ₑ * centralAbsIntegral μA f x ∂μG < ⊤ := by
  obtain ⟨H₁, hH₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hφ
  obtain ⟨H₂, hH₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hf
  have hφm : Measurable φ := (continuous_of_mem_levelSubmodule hH₁).measurable
  have hfm : Measurable f := (continuous_of_mem_levelSubmodule hH₂).measurable
  have hφA : ∀ g : G, Measurable fun a : A => ‖φ ((a : G) * g)‖ₑ := fun g =>
    (hφm.comp (continuous_subtype_val.mul continuous_const).measurable).enorm
  have hmq : Measurable fun q : LeftQuotient A => centralAbsIntegral μA φ q.out ^ 2 :=
    ((continuous_out_of_invariant (continuous_centralAbsIntegral hH₁)
      (centralAbsIntegral_mul_left φ)).measurable).pow_const 2
  calc ∫⁻ x, ‖φ x‖ₑ * centralAbsIntegral μA f x ∂μG
      = ∫⁻ q, ∫⁻ a, (fun g => ‖φ g‖ₑ * centralAbsIntegral μA f g) ((a : G) * q.out) ∂μA ∂ν :=
        (lintegral_lintegral_out_eq hA hν (hφm.enorm.mul (measurable_centralAbsIntegral hfm))).symm
    _ = ∫⁻ q, centralAbsIntegral μA φ q.out * centralAbsIntegral μA f q.out ∂ν := by
        refine lintegral_congr fun q => ?_
        simp only [centralAbsIntegral_mul_left]
        rw [lintegral_mul_const _ (hφA q.out)]
        rfl
    _ ≤ ∫⁻ q, (centralAbsIntegral μA φ q.out ^ 2 + centralAbsIntegral μA f q.out ^ 2) ∂ν :=
        lintegral_mono fun q => ennreal_mul_le_sq_add_sq _ _
    _ = ∫⁻ q, centralAbsIntegral μA φ q.out ^ 2 ∂ν +
          ∫⁻ q, centralAbsIntegral μA f q.out ^ 2 ∂ν := lintegral_add_left hmq _
    _ < ⊤ := ENNReal.add_lt_top.mpr
        ⟨lintegral_centralAbsIntegral_out_sq_lt_top hA hν hw hL hφm hH₁.2,
          lintegral_centralAbsIntegral_out_sq_lt_top hA hν hw hL hfm hH₂.2⟩

variable {H : Subgroup G} [MeasurableSpace H] [BorelSpace H] {μH : Measure H}
  [IsFiniteMeasure μH]

include hA in
/-- **Absolute convergence of the triple integral of VIII.4.1 from central and `L²` weights.**
Let `E` and `φ` lie in the Schwartz space, let `E(x⁻¹) = E(x)` and let `φ` be left
`H`-invariant. Suppose that the left translate `x ↦ E(g⁻¹ x)` lies in the Schwartz space. Then
`(g', a, h) ↦ E(g'⁻¹ h a g) φ(g')` is integrable on `G × A × H`. After the substitution
`g' ↦ h g'`, the identity `E(g'⁻¹ a g) = E(g⁻¹ a⁻¹ g')` and the inversion invariance of `μ_A`
reduce the integral to `μ_H(H) ∫_G |φ| Φ`, with `Φ` the central absolute integral of the
translate. That integral is finite by `lintegral_enorm_mul_centralAbsIntegral_lt_top`. -/
theorem integrable_kernelTriple_of_l2Weights [MeasurableMul A] [MeasurableInv A]
    [μA.IsInvInvariant] [Nonempty (CompactOpenSubgroup G)] [μG.IsMulLeftInvariant] [SFinite μG]
    (hν : IsCompatible A μG μA ν) (hw : CentralWeights μA Ξ σ) (hL : L2Weights μG Ξ σ)
    {E φ : G → ℂ} (hE : E ∈ schwartzSubmodule Ξ σ) (hφ : φ ∈ schwartzSubmodule Ξ σ)
    (hEinv : ∀ x, E x⁻¹ = E x) (hφH : ∀ h ∈ H, ∀ x, φ (h * x) = φ x) (g : G)
    (hEg : (fun x => E (g⁻¹ * x)) ∈ schwartzSubmodule Ξ σ) :
    Integrable (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1)
      (μG.prod (μA.prod μH)) := by
  obtain ⟨H₁, hH₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hE
  obtain ⟨H₂, hH₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp hφ
  have hEc : Continuous E := continuous_of_mem_levelSubmodule hH₁
  have hφc : Continuous φ := continuous_of_mem_levelSubmodule hH₂
  set f : G → ℂ := fun x => E (g⁻¹ * x) with hfdef
  have hfm : Measurable f := (hEc.comp (continuous_const.mul continuous_id)).measurable
  have hmeas : Measurable
      (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1) :=
    (hEc.measurable.comp ((measurable_fst.inv.mul (continuous_subtype_val.measurable.comp
      (measurable_snd.comp measurable_snd))).mul ((continuous_subtype_val.measurable.comp
        (measurable_fst.comp measurable_snd)).mul measurable_const))).mul
      (hφc.measurable.comp measurable_fst)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  -- the integrand after the substitution `g' ↦ h g'`
  set J : A → G → ℝ≥0∞ := fun a x => ‖φ x‖ₑ * ‖f (((a : G))⁻¹ * x)‖ₑ with hJ
  have hJm : Measurable (Function.uncurry J) :=
    (hφc.measurable.comp measurable_snd).enorm.mul
      (hfm.comp ((continuous_subtype_val.measurable.comp measurable_fst).inv.mul
        measurable_snd)).enorm
  have hinner : ∀ q : A × H,
      ∫⁻ x, ‖E (x⁻¹ * q.2 * ((q.1 : G) * g)) * φ x‖ₑ ∂μG = ∫⁻ x, J q.1 x ∂μG := by
    rintro ⟨a, h⟩
    rw [(lintegral_mul_left_eq_self
      (fun x => ‖E (x⁻¹ * h * ((a : G) * g)) * φ x‖ₑ) (h : G) (μ := μG)).symm]
    refine lintegral_congr fun x => ?_
    simp only [hJ, hfdef]
    rw [hφH h h.2 x, enorm_mul, mul_comm]
    congr 2
    rw [← hEinv]
    congr 1
    group
  have hJA : ∀ x, ∫⁻ a, J a x ∂μA = ‖φ x‖ₑ * centralAbsIntegral μA f x := by
    intro x
    simp only [hJ]
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    congr 1
    have h := lintegral_inv_eq_self (μ := μA) (fun a : A => ‖f ((a : G) * x)‖ₑ)
    simp only [InvMemClass.coe_inv] at h
    exact h
  calc ∫⁻ p, ‖E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1‖ₑ ∂(μG.prod (μA.prod μH))
      = ∫⁻ q, ∫⁻ x, ‖E (x⁻¹ * q.2 * ((q.1 : G) * g)) * φ x‖ₑ ∂μG ∂(μA.prod μH) :=
        lintegral_prod_symm _ hmeas.enorm.aemeasurable
    _ = ∫⁻ q, ∫⁻ x, J q.1 x ∂μG ∂(μA.prod μH) := lintegral_congr hinner
    _ = (∫⁻ a, ∫⁻ x, J a x ∂μG ∂μA) * μH Set.univ := by
        rw [lintegral_prod (fun q : A × H => ∫⁻ x, J q.1 x ∂μG)
          (hJm.lintegral_prod_right'.comp measurable_fst).aemeasurable]
        simp only [lintegral_const]
        exact lintegral_mul_const _ hJm.lintegral_prod_right'
    _ = (∫⁻ x, ‖φ x‖ₑ * centralAbsIntegral μA f x ∂μG) * μH Set.univ := by
        rw [lintegral_lintegral_swap hJm.aemeasurable]
        simp only [hJA]
    _ < ⊤ := ENNReal.mul_lt_top
        (lintegral_enorm_mul_centralAbsIntegral_lt_top hA hν hw hL hφ hEg)
        (measure_lt_top μH Set.univ)

end SquareBound

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local instance rationalKernelLocalStepSecondCountable :
    SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalKernelLocalStepT2 : T2Space (rationalPoints G) :=
  rationalPoint_t2Space F G

/-- **The local kernel step of VIII.4.1 from central and `L²` weights.** Let `H` be a compact
open subgroup, `muG` a two-sided Haar measure on `G(F)`, `muA` a Haar measure on `A_G(F)` and
`χ` a unitary character. Let `E` have the properties of `°e_H`
(`IsRationalCuspidalLevelKernel`). Assume the central weights and the `L²` weights of the
actual `Ξ` and `σ`, and the diagonal input. Then the actual central level span is finite
dimensional. -/
theorem IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_l2Weights
    (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ) (hχ : IsUnitaryCharacter χ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure] [muG.IsMulRightInvariant]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    {E : RationalSchwartzSpace hKc hPK ρ} (hE : IsRationalCuspidalLevelKernel hKc hPK ρ muG H E)
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hL : L2Weights muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hdiag : RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E) :
    FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) := by
  have hA : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) :=
    isClosed_range_splitComponent G s hs
  have hAc : (rationalPoints.map s).range ≤ Subgroup.center (rationalPoints G) :=
    hs.isCentralSplitTorus.isCentral.range_le_center
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  have : LocallyCompactSpace (rationalPoints.map s).range :=
    hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (rationalPoints.map s).range :=
    inferInstanceAs (SecondCountableTopology
      ((rationalPoints.map s).range : Set (rationalPoints G)))
  have : muA.IsMulRightInvariant := isMulRightInvariant_of_le_center hAc muA
  have : muA.IsInvInvariant := isInvInvariant_of_le_center hAc muA
  have : (levelMeasure muG H).IsMulLeftInvariant := levelMeasure_isMulLeftInvariant muG H
  have : IsFiniteMeasure (levelMeasure muG H) := levelMeasure_isFiniteMeasure muG H hHc
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  let : MeasurableSpace (LeftQuotient (rationalPoints.map s).range) := borel _
  have : BorelSpace (LeftQuotient (rationalPoints.map s).range) := ⟨rfl⟩
  obtain ⟨muQ, hQ⟩ := @compatibleMeasureExists (rationalPoints G) _ _ _ _ _ _ _
    (rationalPoints.map s).range hA _ _ muG muA _ _ _ _ _ _ _ _
  have hTW := rationalTranslationWeights K.isOpen hKc hPK ρ
  have hmes := levelMeasure_univ_toReal_ne_zero muG H hHc
  have hW : ∀ φ ∈ rationalCuspidalLevel hKc hPK ρ H.toSubgroup,
      ∀ h ∈ H.toSubgroup, ∀ x, (φ : rationalPoints G → ℂ) (h * x) = φ x := by
    intro φ hφ h hh x
    simpa using hφ.2 h hh 1 H.one_mem x
  refine finiteDimensional_schwartzCentralIntegralSpan_of_kernel hA hQ hAc hχ hE.conj_eq hmes
    (CentralWeights.convergesOn _ muA χ hw hχ) hW ?_ ?_ ?_ ?_ (hdiag muQ hQ)
  · intro φ hφ x
    rw [hE.convolution_eq φ hφ x, levelMeasure_univ]
  · intro φ hφ g
    have hEg : (fun x => (E : rationalPoints G → ℂ) (g⁻¹ * x)) ∈
        schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ) := by
      have h := Space.coe_mem (Space.translate hTW 1 g E)
      have e : ((Space.translate hTW 1 g E : RationalSchwartzSpace hKc hPK ρ) :
          rationalPoints G → ℂ) = fun x => (E : rationalPoints G → ℂ) (g⁻¹ * x) := by
        funext x
        simp
      rwa [e] at h
    exact integrable_kernelTriple_of_l2Weights hA hQ hw hL (Space.coe_mem E) (Space.coe_mem φ)
      hE.inv_eq (hW φ hφ) g hEg
  · intro y
    obtain ⟨ψ, hψS, hψ⟩ := exists_mem_eq_integral_kernel (μH := levelMeasure muG H) H.isOpen hTW
      (fun f hf g => translate_mem_rationalCuspidalSubmodule hKc hPK ρ hTW hf 1 g)
      hE.mem_level.1 hE.inv_eq (fun k hk x => by simpa using hE.mem_level.2 1 H.one_mem k hk x) y
    refine ⟨((((levelMeasure muG H Set.univ).toReal : ℂ)⁻¹) ^ 2) • ψ, ⟨?_, ?_⟩, ?_⟩
    · exact (rationalCuspidalSubmodule hKc hPK ρ).smul_mem _ hψS
    · rw [SetLike.mem_coe, Submodule.mem_comap, map_smul, Space.toFunLinear_apply, hψ]
      change IsBiInvariant H.toSubgroup _
      intro k₁ hk₁ k₂ hk₂ g
      have hb := isBiInvariant_integral_kernel (μH := levelMeasure muG H) hE.mem_level.2 y
        k₁ hk₁ k₂ hk₂ g
      simp only [Space.toFunLinear_apply] at hb
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb]
    · funext g
      simp only [kernelAlphaChi]
      congr 1
      funext g'
      simp only [Space.coe_smul, Pi.smul_apply, smul_eq_mul, hψ, kernelAlpha]
  · intro φ _ φ' _
    exact integrable_centralProjection_mul_conj_out hA hQ hAc hw hL hχ (Space.coe_mem φ)
      (Space.coe_mem φ')

/-- **The local kernel step of VIII.4.1 from VIII.3.2 at `E`.** For connected reductive `G`,
a Haar measure `muG` (right invariant by `rationalHaar_isMulRightInvariant`), `E` with the
properties of `°e_H`, the central and `L²` weights, and the VIII.3.2 integrability form at `E`
(`RationalLevelKernelConjugationIntegrable`), the actual central level span is finite
dimensional. If `χ` is nontrivial on `A_G(F) ∩ H` the span is zero
(`rationalCuspidalCentralLevel_finite_of_ne_one`). Otherwise the diagonal input comes from
`IsRationalCuspidalLevelKernel.diagonalIntegrable` and
`RationalLevelKernelPairingIntegrable.of_leftConjugationPairing`. -/
theorem IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_conjugationIntegrable
    (hG : IsConnectedReductive G) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ) (hχ : IsUnitaryCharacter χ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    {E : RationalSchwartzSpace hKc hPK ρ} (hE : IsRationalCuspidalLevelKernel hKc hPK ρ muG H E)
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hL : L2Weights muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (h32 : RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E) :
    FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) := by
  by_cases hb : ∃ b : (rationalPoints.map s).range, (b : rationalPoints G) ∈ H ∧ χ b ≠ 1
  · obtain ⟨b, hbH, hχb⟩ := hb
    exact (rationalCuspidalCentralLevel_finite_of_ne_one hKc hPK ρ muA χ H.toSubgroup hbH
      hχb).2
  · push Not at hb
    have := rationalHaar_isMulRightInvariant hG muG
    exact hE.finiteDimensional_levelSpan_of_l2Weights hKc hPK ρ hs muA χ hχ muG H hHc hw hL
      (hE.diagonalIntegrable hKc hPK ρ hG hs muA χ muG H hHc hb
        (RationalLevelKernelPairingIntegrable.of_leftConjugationPairing hKc hPK ρ hs muA muG H
          hHc E h32))

end Rational

/-- **The local kernel step of VIII.4.1, for every structural choice.** For a connected
reductive `G` over a nonarchimedean local field with the parameters of
`RationalCuspidalCentralProjectionFiniteStatement` (a maximal split torus, a generic
cocharacter, a compact open `K` with `G(F) = P₀(F) K`, a closed matrix representation `ρ`, a
split component `s`, a Haar measure `muA` on `A_G(F)` and a unitary character `χ`), every compact
open `H`, every Haar measure `muG` on `G(F)` and every `E` in the actual Schwartz space: if `E`
has the properties of `°e_H` (`IsRationalCuspidalLevelKernel`) and satisfies the VIII.3.2
integrability form (`RationalLevelKernelConjugationIntegrable`), then the actual central level
span of `H` is finite dimensional. -/
def RationalCuspidalLevelKernelFiniteStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), IsUnitaryCharacter χ →
    ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
    ∀ (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
      (E : RationalSchwartzSpace hKc hPK ρ),
      IsRationalCuspidalLevelKernel hKc hPK ρ muG H E →
      RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E →
      FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup)

/-- **The local kernel step from three Library statements.** The heights on the split centre
(`RationalSplitCenterHeightStatement`, giving the central weights), Lemma II.1.5
(`RationalXiSquareIntegrableStatement`, giving the `L²` weights) and the special-vertex compact
inputs (`RationalSpecialVertexCompactInputsStatement`, supplying the compact open `K0` with a
simultaneous standard basis and the finite Cartan covering that II.1.5 needs) give
`RationalCuspidalLevelKernelFiniteStatement`. -/
theorem RationalCuspidalLevelKernelFiniteStatement.of_statements
    (hcen : RationalSplitCenterHeightStatement.{u})
    (hsq : RationalXiSquareIntegrableStatement.{u})
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}) :
    RationalCuspidalLevelKernelFiniteStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _ χ hχ H hHc muG _ E hE h32
  obtain ⟨D, x, -, hprops, hbasis, hcover⟩ := hSV F G hG S i hi ν hν
  have hw := RationalSplitCenterHeightStatement.centralWeights K.isOpen hKc hPK ρ hcen hG hs hρ
    muA
  have hL := RationalXiSquareIntegrableStatement.l2Weights hsq hG hi hν hprops.2.1.2.1
    hprops.2.1.1 hbasis hcover (K := K.toSubgroup) K.isOpen hKc hPK hρ muG
  exact hE.finiteDimensional_levelSpan_of_conjugationIntegrable hKc hPK ρ hG hs muA χ hχ muG H
    hHc hw hL h32

end Langlands.HarishChandraSchwartz
