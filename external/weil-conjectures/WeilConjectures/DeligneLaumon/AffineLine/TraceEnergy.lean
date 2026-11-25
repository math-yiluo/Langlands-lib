/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.EReal.Operations
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.CurveEndpoints
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.EulerProduct
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.LSeries
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.WeilSheaf.StalkTensorTrace
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.WeilSheaf.TraceFunctionOps
public import WeilConjectures.WeilSheaf.UpperStarLowerStar
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.AlgebraicGeometry.AffineSpace.GeometricallyConnected
public import WeilConjectures.PointCountFiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.PointCountBound
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Detecting a weight from the growth of the squared trace sums

For a lisse Weil sheaf `N` on a variety over `𝔽_q` the *trace energy* is the sum of the
squared complex absolute values of its trace function over the `𝔽_{qⁿ}`-points,

`S_n(X₀, N) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{N,n}(x)|²`.

Its exponential generating series is the `L`-function of `N ⊗ N^∨(w)` on a curve, hence a
ratio of two determinants, and the denominator is pure of weight `2v + 2` by the endpoint
lemma `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`. The
series has infinitely many nonzero coefficients because the summands are nonnegative and not
all zero, so at least one finite pole survives; an energy bound `S_n ≤ C q^{nB}` forces the
radius of convergence to be at least `q^{-B}`, so that pole cannot lie inside, giving
`v ≤ B - 1`. No weight estimate for `H_c^1` is used.

The proof goes through the `L²`-weight parameter `‖N‖`, the exponent of growth of the trace
energies: the energy bound gives `‖N‖ ≤ B - 1`, and the `L²`-rigidity gives `‖N‖ = v` for a
nonzero lisse punctually pure `N`. The rigidity is deduced from the case of `ι`-real sheaves by
passing to the normalized real envelope `N⁰ ⊕ (N⁰)^∨` of the constant twist `N⁰` of weight `0`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.traceEnergy`: the sum `S_n(X₀, N)`.
- `AlgebraicGeometry.WeilSheaf.l2Weight`: the `L²`-weight parameter `‖F‖`.
- `AlgebraicGeometry.WeilSheaf.l2Series`: the `L²`-series `φ_F(t) = ∑ S_m t^{m - 1}`.
- `AlgebraicGeometry.WeilSheaf.realEnvelope`: the normalized real envelope, lisse for lisse `F`
  (`AlgebraicGeometry.WeilSheaf.IsLisse.realEnvelope`).
- `AlgebraicGeometry.WeilSheaf.lt_l2Weight_iff`: the radius of `φ_F` is `q^{-‖F‖ - 1}`.
- `AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight`: `‖G‖ = w` for a nonzero
  lisse sheaf pure of weight `w`.
- `AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le`: the weight bound it detects.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.l2Weight_directImage`: `‖j_*M‖ = ‖M‖ = w`.

## Implementation notes

The analytic part (the `L²`-weight, its radius characterisation and the energy bound) is proved
in general.

The `L²`-rigidity for real sheaves uses the Euler product of the `L`-series of `G ⊗ G` on the
curve (`AlgebraicGeometry.WeilSheaf.lSeries_mul_localPolynomial_compactlySupportedCohomology_two`,
the Grothendieck–Lefschetz trace formula) and the purity of `H_c²`
(`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two` for the
identity of the curve).
-/

@[expose] public section

universe u

open CategoryTheory Filter Topology

open scoped PowerSeries.WithPiTopology

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace energy `S_n(X₀, F) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{F,n}(x)|²` of a Weil sheaf at
level `n`, the squared `L²`-norm of its trace function on the `𝔽_{qⁿ}`-points, with junk value
`0` if `X₀` has infinitely many `𝔽_{qⁿ}`-points. The intended situation is that of
`AlgebraicGeometry.Scheme.Hom.finite_fieldPoints`, where `X₀` is of finite type over the finite
field `k₀` and the index type is finite. -/
noncomputable def traceEnergy (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) : ℝ :=
  ∑ᶠ x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n),
    ‖ι (F.traceFunction n x)‖ ^ 2

/-- The trace energy is nonnegative, as a sum of squares. -/
theorem traceEnergy_nonneg (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) :
    0 ≤ F.traceEnergy ι n :=
  finsum_nonneg fun _ ↦ sq_nonneg _

/-- The *`L²`-weight parameter* `‖F‖` of a Weil sheaf, the exponent of growth of its trace
energies `S_m = ‖f_F‖²_m` (`AlgebraicGeometry.WeilSheaf.traceEnergy`):

`‖F‖ = sup {β ∈ ℝ | limsup_{m → ∞} S_m / q^{m(β + 1)} > 0}`,

the supremum of the empty set being `-∞`, the exponent `1` being the dimension of the curve on
which `F` is intended to live. The `limsup` is taken in `ℝ≥0∞`.
(blueprint: `definition-growth-squared-traces`) -/
noncomputable def l2Weight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : EReal :=
  ⨆ (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
    (F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop), (β : EReal)

/-- The *`L²`-series* `φ_F(t) = ∑_{m ≥ 1} S_m t^{m - 1}` of a Weil sheaf, the power series whose
coefficients are the trace energies `S_m` (`AlgebraicGeometry.WeilSheaf.traceEnergy`). Its
radius of convergence determines the `L²`-weight parameter
(`AlgebraicGeometry.WeilSheaf.lt_l2Weight_iff`).
(blueprint: `lemma-radius-squared-traces--1`) -/
noncomputable def l2Series (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun m ↦ F.traceEnergy ι (m + 1)

section Growth

/-! ### The exponent of growth of a nonnegative sequence -/

variable {q : ℝ} {b : ℕ → ℝ}

private lemma div_rpow_eq_mul_pow (hq : 0 < q) (m : ℕ) (β : ℝ) :
    b m / q ^ ((m : ℝ) * (β + 1)) = b m * (q ^ (-(β + 1))) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, div_eq_mul_inv, ← Real.rpow_neg hq.le]
  congr 2
  ring

private lemma limsup_eq_zero_of_le (hq : 1 < q) {C B : ℝ}
    (hb : ∀ m : ℕ, 1 ≤ m → b m ≤ C * q ^ ((m : ℝ) * B)) {β : ℝ} (hβ : B - 1 < β) :
    limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
  have hq0 : 0 < q := by linarith
  have hr1 : q ^ (B - (β + 1)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hlim : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (C * (q ^ (B - (β + 1))) ^ m)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1).const_mul C
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_).limsup_eq
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  calc b m ≤ C * q ^ ((m : ℝ) * B) := hb m hm
    _ = C * (q ^ (B - (β + 1))) ^ m * q ^ ((m : ℝ) * (β + 1)) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
      congr 2
      ring

private lemma radius_le_of_limsup_pos (hq : 1 < q) {β : ℝ}
    (h : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop) :
    (FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).radius ≤
      ENNReal.ofReal (q ^ (-(β + 1))) := by
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ q ^ (-(β + 1)) := by positivity
  by_contra hlt
  rw [not_le] at hlt
  rw [ENNReal.ofReal_eq_coe_nnreal hρ0] at hlt
  have ht := (Asymptotics.isLittleO_one_iff ℝ).1
    ((FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).isLittleO_one_of_lt_radius hlt)
  simp only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_mk] at ht
  have ht' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (‖b (n + 1)‖ * (q ^ (-(β + 1))) ^ n *
      q ^ (-(β + 1)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (ht.mul_const (q ^ (-(β + 1))))
  have hs : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop
      (𝓝 0) := by
    refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ht' (fun _ ↦ zero_le) fun n ↦ ENNReal.ofReal_le_ofReal ?_)
    rw [div_rpow_eq_mul_pow hq0, pow_succ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hρ0
  exact h.ne' hs.limsup_eq

private lemma limsup_pos_of_radius_lt (hq : 1 < q) (hb : ∀ m, 0 ≤ b m) {β : ℝ}
    (h : (FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).radius <
      ENNReal.ofReal (q ^ (-(β + 1)))) :
    0 < limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop := by
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 < q ^ (-(β + 1)) := by positivity
  refine pos_iff_ne_zero.2 fun h0 ↦ h.not_ge ?_
  have hev := eventually_lt_of_limsup_lt (h0.trans_lt zero_lt_one)
  rw [ENNReal.ofReal_eq_coe_nnreal hρ0.le]
  refine FormalMultilinearSeries.le_radius_of_eventually_le _ (1 / q ^ (-(β + 1))) ?_
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hev] with n hn
  rw [ENNReal.ofReal_lt_one, div_rpow_eq_mul_pow hq0, pow_succ, ← mul_assoc] at hn
  rw [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_mk, Real.norm_eq_abs,
    abs_of_nonneg (hb _), le_div_iff₀ hρ0]
  exact hn.le

private lemma limsup_eq_zero_of_le_mul (hq : 0 ≤ q) {b' : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ m, b' m ≤ K * b m) {β : ℝ}
    (h : limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop = 0) :
    limsup (fun m : ℕ ↦ ENNReal.ofReal (b' m / q ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
  have ht : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop
      (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le zero_le h.le
  have ht' := ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal K)
  rw [mul_zero] at ht'
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
    (fun _ ↦ zero_le) fun m ↦ ?_).limsup_eq
  rw [← ENNReal.ofReal_mul hK, mul_div_assoc']
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb m) (Real.rpow_nonneg hq _))

end Growth

/-- The trace energy bound `S_m ≤ C q^{mB}` for `m ≥ 1` bounds the `L²`-weight parameter:
`‖F‖ ≤ B - 1`. For `β > B - 1` the ratios `S_m / q^{m(β + 1)} ≤ C q^{m(B - β - 1)}` tend to
`0`. -/
theorem l2Weight_le_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    {C B : ℝ} (hS : ∀ n : ℕ, 1 ≤ n → F.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B)) :
    F.l2Weight ι ≤ ((B - 1 : ℝ) : EReal) := by
  refine iSup₂_le fun β hβ ↦ EReal.coe_le_coe_iff.2 (not_lt.1 fun hlt ↦ hβ.ne' ?_)
  exact limsup_eq_zero_of_le (by exact_mod_cast Finite.one_lt_card) hS hlt

/-- The radius of convergence `r_F` of the `L²`-series `φ_F` and the `L²`-weight parameter
`‖F‖` are related by `r_F = q^{-‖F‖ - 1}`, equivalently `‖F‖ = -1 - log_q r_F`, with the
conventions `q^{-∞} = 0` and `q^{∞} = ∞`. This is stated as: for every real `β`,
`β < ‖F‖` if and only if `r_F < q^{-(β + 1)}`. (blueprint: `lemma-radius-squared-traces--1`) -/
theorem lt_l2Weight_iff (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (β : ℝ) :
    (β : EReal) < F.l2Weight ι ↔
      (F.l2Series ι).radius < ENNReal.ofReal ((Nat.card k₀ : ℝ) ^ (-(β + 1))) := by
  have hq : 1 < (Nat.card k₀ : ℝ) := by exact_mod_cast Finite.one_lt_card
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by linarith
  constructor
  · intro h
    obtain ⟨β', h'⟩ := lt_iSup_iff.1 h
    obtain ⟨hpos, hlt⟩ := lt_iSup_iff.1 h'
    refine (radius_le_of_limsup_pos hq hpos).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (by positivity)).2 (Real.rpow_lt_rpow_of_exponent_lt hq ?_))
    linarith [EReal.coe_lt_coe_iff.1 hlt]
  · intro h
    have hc : Tendsto (fun x : ℝ ↦ ENNReal.ofReal ((Nat.card k₀ : ℝ) ^ (-(x + 1)))) (𝓝[>] β)
        (𝓝 (ENNReal.ofReal ((Nat.card k₀ : ℝ) ^ (-(β + 1))))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.rpow (by fun_prop)
        fun _ ↦ Or.inl hq0.ne')).tendsto β).mono_left nhdsWithin_le_nhds
    obtain ⟨β', hβ'r, hββ'⟩ := ((hc.eventually (lt_mem_nhds h)).and self_mem_nhdsWithin).exists
    exact (EReal.coe_lt_coe_iff.2 hββ').trans_le (le_iSup₂_of_le β'
      (limsup_pos_of_radius_lt hq (F.traceEnergy_nonneg ι) hβ'r) le_rfl)

/-- If the trace energies of `F'` are those of `F` divided by `q^{mw}`, then
`‖F'‖ = ‖F‖ - w`: the defining ratio of `F'` at `β` is that of `F` at `β + w`. -/
theorem l2Weight_eq_sub_of_traceEnergy_eq (ι : PadicAlgCl l →+* ℂ) (F F' : WeilSheaf k₀ l X)
    {w : ℝ} (h : ∀ m : ℕ, F'.traceEnergy ι m =
      F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w)) :
    F'.l2Weight ι = F.l2Weight ι - w := by
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by exact_mod_cast Nat.card_pos
  have key : ∀ β : ℝ, (fun m : ℕ ↦ ENNReal.ofReal
      (F'.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) =
      fun m : ℕ ↦ ENNReal.ofReal
        (F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((β + w) + 1))) := by
    refine fun β ↦ funext fun m ↦ congrArg ENNReal.ofReal ?_
    rw [h, div_div, ← Real.rpow_add hq0]
    congr 2
    ring
  refine le_antisymm (iSup₂_le fun β hβ ↦ ?_) ?_
  · rw [key] at hβ
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot w)) (.inl (EReal.coe_ne_top w))]
    exact_mod_cast le_iSup₂_of_le (f := fun (γ : ℝ) _ ↦ (γ : EReal)) (β + w) hβ le_rfl
  · rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot w)) (.inl (EReal.coe_ne_top w))]
    refine iSup₂_le fun γ hγ ↦ ?_
    have hγ' : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (F'.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((γ - w) + 1)))) atTop := by
      rwa [key, sub_add_cancel]
    have := le_iSup₂_of_le (f := fun (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (F'.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop) ↦ (β : EReal))
      (γ - w) hγ' le_rfl
    calc (γ : EReal) = ((γ - w : ℝ) : EReal) + w := by norm_cast; ring
      _ ≤ F'.l2Weight ι + w := by gcongr; exact this

/-- If the trace energies of `E` are bounded by a constant multiple of those of `F`, then
`‖E‖ ≤ ‖F‖`: a positive `limsup` for `E` at `β` forces a positive `limsup` for `F` at `β`. -/
theorem l2Weight_le_of_traceEnergy_le_mul (ι : PadicAlgCl l →+* ℂ) (E F : WeilSheaf k₀ l X)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ m : ℕ, E.traceEnergy ι m ≤ K * F.traceEnergy ι m) :
    E.l2Weight ι ≤ F.l2Weight ι :=
  iSup₂_le fun β hβ ↦ le_iSup₂_of_le β
    (pos_iff_ne_zero.2 fun h0 ↦ hβ.ne' (limsup_eq_zero_of_le_mul (Nat.cast_nonneg _) hK h h0))
    le_rfl

/-- If the trace energies of `E` are bounded by those of `F`, then `‖E‖ ≤ ‖F‖`; here `E` and
`F` may live on different schemes, e.g. a sheaf on a dense open and its direct image. -/
theorem l2Weight_le_l2Weight_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ)
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l X)
    (F : WeilSheaf k₀ l Y) (h : ∀ m : ℕ, E.traceEnergy ι m ≤ F.traceEnergy ι m) :
    E.l2Weight ι ≤ F.l2Weight ι :=
  iSup₂_le fun β hβ ↦ le_iSup₂_of_le β (pos_iff_ne_zero.2 fun h0 ↦ hβ.ne'
    (limsup_eq_zero_of_le_mul (Nat.cast_nonneg _) zero_le_one (fun m ↦ (one_mul
      (F.traceEnergy ι m)).symm ▸ h m) h0)) le_rfl

/-- If the trace energies of `E` exceed those of `F` by at most `C q^{mB}`, then
`‖E‖ ≤ max ‖F‖ (B - 1)`: for `β` above both bounds the defining ratio of `E` at `β` is at most
that of `F`, of `limsup` zero, plus `C q^{m(B - β - 1)}`, which tends to zero. -/
theorem l2Weight_le_max_of_traceEnergy_le_add (ι : PadicAlgCl l →+* ℂ)
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l X)
    (F : WeilSheaf k₀ l Y) {C B : ℝ} (h : ∀ m : ℕ, E.traceEnergy ι m ≤
      F.traceEnergy ι m + C * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * B)) :
    E.l2Weight ι ≤ max (F.l2Weight ι) ((B - 1 : ℝ) : EReal) := by
  have hq : 1 < (Nat.card k₀ : ℝ) := by exact_mod_cast Finite.one_lt_card
  refine iSup₂_le fun β hβ ↦ not_lt.1 fun hlt ↦ hβ.ne' ?_
  rw [max_lt_iff] at hlt
  have hF : limsup (fun m : ℕ ↦ ENNReal.ofReal
      (F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
    by_contra hne
    exact hlt.1.not_ge (le_iSup₂_of_le (f := fun (γ : ℝ) (_ : 0 < limsup (fun m : ℕ ↦
      ENNReal.ofReal (F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (γ + 1)))) atTop) ↦
        (γ : EReal)) β (pos_iff_ne_zero.2 hne) le_rfl)
  have hC := limsup_eq_zero_of_le (b := fun m : ℕ ↦ C * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * B)) hq
    (fun _ _ ↦ le_rfl) (EReal.coe_lt_coe_iff.1 hlt.2)
  have ht := (tendsto_of_le_liminf_of_limsup_le zero_le hF.le).add
    (tendsto_of_le_liminf_of_limsup_le zero_le hC.le)
  rw [add_zero] at ht
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ zero_le)
    fun m ↦ (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le).limsup_eq
  rw [← add_div]
  exact div_le_div_of_nonneg_right (h m) (by positivity)

section Envelope

/-- The *normalized real envelope* `Env_ι(F; b) = F⁰ ⊕ (F⁰)^∨` of a lisse Weil sheaf, where
`F⁰ = F ⊗ 𝓑_b` is the constant Weil twist `AlgebraicGeometry.WeilSheaf.constantTwist` by
`b`. It is meant for `F` punctually `ι`-pure of weight `w` and `|ι b| = q^{-w/2}`, for instance
`b = ι⁻¹(q^{-w/2})` when `ι` is an isomorphism; then `F⁰` is pure of weight `0` and the
envelope is `ι`-real (`AlgebraicGeometry.WeilSheaf.isReal_realEnvelope`).
(blueprint: `proposition-twisting-weight-zero-adding-dual--3`) -/
noncomputable def realEnvelope (F : WeilSheaf k₀ l X) (hF : F.IsLisse) (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l X :=
  F.constantTwist b ⊞ (F.constantTwist b).dual (hF.constantTwist (b := b))

/-- The constant twist of a nonzero Weil sheaf is nonzero, the underlying étale sheaf being the
same. -/
theorem not_isZero_constantTwist {F : WeilSheaf k₀ l X} (hF : ¬ Limits.IsZero F)
    (b : (PadicAlgCl l)ˣ) : ¬ Limits.IsZero (F.constantTwist b) :=
  fun h ↦ hF (isZero_iff_isZero_carrier.2
    ((isZero_iff_isZero_carrier (F := F.constantTwist b)).1 h))

/-- The envelope of a nonzero lisse Weil sheaf is nonzero: it contains the nonzero constant
twist `F ⊗ 𝓑_b` as a summand. -/
theorem not_isZero_realEnvelope {F : WeilSheaf k₀ l X} (hF : ¬ Limits.IsZero F)
    (hlisse : F.IsLisse) (b : (PadicAlgCl l)ˣ) : ¬ Limits.IsZero (F.realEnvelope hlisse b) :=
  fun h ↦ not_isZero_constantTwist hF b (h.of_mono (Limits.biprod.inl (X := F.constantTwist b)))

/-- The envelope of a lisse Weil sheaf is lisse, as a sum of a constant twist and its dual. -/
theorem IsLisse.realEnvelope {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (b : (PadicAlgCl l)ˣ) :
    (F.realEnvelope hF b).IsLisse :=
  (hF.constantTwist (b := b)).biprod (hF.constantTwist (b := b)).dual

/-- The envelope `Env_ι(F; b)` of a lisse sheaf `F` punctually `ι`-pure of weight `w`, with
`|ι b| = q^{-w/2}`, is `ι`-real: at a closed point the eigenvalues `β_j` of `F⁰` have
`|ι β_j| = 1`, so those of the dual summand are `ι(β_j⁻¹) = conj (ι β_j)`, and the local
eigenvalue multiset is stable under complex conjugation.
(blueprint: `proposition-twisting-weight-zero-adding-dual--5`) -/
theorem isReal_realEnvelope {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) :
    (F.realEnvelope hF b).IsReal ι := by
  intro x
  obtain ⟨e⟩ := nonempty_equiv_stalk_biprod (F.constantTwist b)
    ((F.constantTwist b).dual (hF.constantTwist (b := b))) x
  obtain ⟨e'⟩ := nonempty_equiv_stalk_dual (hF.constantTwist (b := b)) x
  refine ((h.constantTwist_zero hb x).isReal_prod_dual
    (pow_pos Nat.card_pos _)).of_localPolynomial_eq (e.localPolynomial_eq.trans ?_)
  rw [FrobeniusModule.localPolynomial_prod, FrobeniusModule.localPolynomial_prod,
    e'.localPolynomial_eq]

/-- The envelope of a punctually `ι`-pure sheaf of weight `w`, with `|ι b| = q^{-w/2}`, is
punctually `ι`-pure of weight `0`: `F⁰` is by
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.constantTwist`, its dual has the inverse
eigenvalues, of absolute value `1`, and a direct sum of pure sheaves of weight `0` is pure of
weight `0`. -/
theorem IsPunctuallyPureOfWeight.realEnvelope {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) (hF : F.IsLisse) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) :
    (F.realEnvelope hF b).IsPunctuallyPureOfWeight ι 0 := by
  intro x
  obtain ⟨e⟩ := nonempty_equiv_stalk_biprod (F.constantTwist b)
    ((F.constantTwist b).dual (hF.constantTwist (b := b))) x
  obtain ⟨e'⟩ := nonempty_equiv_stalk_dual (hF.constantTwist (b := b)) x
  have h0 := h.constantTwist_zero hb x
  have h0' := h0.dual
  rw [neg_zero] at h0'
  exact (h0.prod (h0'.of_equiv e')).of_equiv e

/-- The trace energies of the constant twist `F ⊗ 𝓑_b` with `|ι b| = q^{-w/2}` are those of `F`
divided by `q^{mw}`: the twist has trace function `t_{F ⊗ 𝓑_b}(y) = bᵐ t_F(y)` at
`y ∈ X₀(𝔽_{qᵐ})`. -/
theorem traceEnergy_constantTwist (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    {b : (PadicAlgCl l)ˣ} {w : ℝ} (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) (m : ℕ) :
    (F.constantTwist b).traceEnergy ι m =
      F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) := by
  have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
  rw [traceEnergy, traceEnergy, div_eq_mul_inv, finsum_mul]
  refine finsum_congr fun y ↦ ?_
  rw [traceFunction_constantTwist, map_mul, norm_mul, mul_pow, map_pow, norm_pow, hb,
    mul_comm, ← pow_mul, ← Real.rpow_natCast _ (m * 2), ← Real.rpow_mul hq.le,
    ← Real.rpow_neg hq.le]
  congr 2
  push_cast
  ring

/-- The trace energies of the envelope are at most four times those of `F⁰ = F ⊗ 𝓑_b`, for `F`
punctually pure of weight `w` and `|ι b| = q^{-w/2}`: the trace of the envelope is
`t_{F⁰} + conj t_{F⁰} = 2 Re t_{F⁰}`, and `|Re z|² ≤ |z|²`. The finiteness hypotheses make the
sums finite. -/
theorem traceEnergy_realEnvelope_le (ι : PadicAlgCl l →+* ℂ)
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) (m : ℕ) :
    (F.realEnvelope hF b).traceEnergy ι m ≤ 4 * (F.constantTwist b).traceEnergy ι m := by
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  have := (X ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints (FiniteField.galoisExtension k₀ m)
  have : Fintype ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ m)) := Fintype.ofFinite _
  have h0 := h.constantTwist_zero hb
  rw [traceEnergy, traceEnergy, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  rw [realEnvelope, traceFunction_biprod, map_add, map_traceFunction_dual _ h0, Complex.add_conj,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have := Complex.abs_re_le_norm (ι ((F.constantTwist b).traceFunction m y))
  nlinarith [abs_nonneg (ι ((F.constantTwist b).traceFunction m y)).re, sq_abs
    (ι ((F.constantTwist b).traceFunction m y)).re]

/-- A nonzero Weil sheaf on a `k₀`-scheme locally of finite type, punctually `ι`-pure of weight
`w`, admits a unit `b` with `|ι b| = q^{-w/2}`: if `α` is an eigenvalue of the local Frobenius
at a closed point of degree `d` with nonzero stalk, then `|ι α| = q^{dw/2}`, and `b` can be taken
to be a `d`-th root of `α⁻¹`. -/
theorem exists_norm_eq_of_isPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ)
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X) (hF : ¬ Limits.IsZero F) {w : ℝ}
    (h : F.IsPunctuallyPureOfWeight ι w) :
    ∃ b : (PadicAlgCl l)ˣ, ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2) := by
  obtain ⟨x, hx⟩ := F.exists_nontrivial_stalk_of_not_isZero hF
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (F.stalk x).frobeniusEnd
  have hα0 : α ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hv
    exact hv.2 ((F.stalk x).frobenius.map_eq_zero_iff.1 hv.1)
  set d := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  have hd : 0 < d := by
    have : Finite (X.residueField x.1) := x.2
    let := ((X ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap x.1).toAlgebra
    have : Module.Finite k₀ (X.residueField x.1) := Module.Finite.of_finite
    exact Module.finrank_pos
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq α⁻¹ hd
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hα0 (by rw [← hc, zero_pow hd.ne'])
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by exact_mod_cast Nat.card_pos
  have hαn := h x α hα
  simp only [Scheme.Hom.residueCard, Nat.cast_pow] at hαn
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) hd.ne').1 ?_
  rw [Units.val_mk0, ← norm_pow, ← map_pow, hc, map_inv₀, norm_inv, hαn, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le, ← Real.rpow_neg hq0.le]
  congr 1
  ring

end Envelope

/-- If `F` is a lisse Weil sheaf on a smooth affine curve `V` over `k₀`, punctually `ι`-mixed of
weights at most `w`, then `S_m(F) ≤ C q^{m(w + 1)}` for some `C` and all `m ≥ 1`: at
`y ∈ V(𝔽_{qᵐ})` the eigenvalues of the Frobenius have absolute value at most `q^{mw/2}`, so
`|ι t_F(y)|² ≤ r² q^{mw}` for a bound `r` of the rank of `F`, and
`S_m ≤ r² · #V(𝔽_{qᵐ}) · q^{mw} ≤ C q^{m(w + 1)}` by the linear growth of the point counts of an
affine curve. (blueprint: `lemma-bounds-squared-traces--2`) -/
theorem exists_traceEnergy_le_of_hasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l V) (hlisse : F.IsLisse) {w : ℝ} (h : F.HasWeightsAtMost ι w) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      F.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * (w + 1)) := by
  have : LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀)) := by
    have := SmoothOfRelativeDimension.smooth 1 (V ↘ Spec (CommRingCat.of k₀))
    infer_instance
  obtain ⟨N, hN⟩ := hlisse.exists_forall_finrank_stalk_le
  obtain ⟨d, hd⟩ := (V ↘ Spec (CommRingCat.of k₀)).exists_pointCount_le_mul_pow
    (topologicalKrullDim_le_of_smoothOfRelativeDimension (V ↘ Spec (CommRingCat.of k₀)) 1)
  have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
  refine ⟨d * N ^ 2, fun n hn ↦ ?_⟩
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have := (V ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints (FiniteField.galoisExtension k₀ n)
  let := Fintype.ofFinite ((V ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ n))
  have hcard : (Fintype.card ((V ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) : ℝ) ≤ d * (Nat.card k₀ : ℝ) ^ n := by
    have := hd n (by omega)
    rw [Scheme.Hom.pointCount, Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  rw [traceEnergy, finsum_eq_sum_of_fintype]
  calc ∑ y, ‖ι (F.traceFunction n y)‖ ^ 2
      ≤ ∑ _y : (V ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n),
          ((N : ℝ) * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n) ^ 2 :=
        Finset.sum_le_sum fun y _ ↦ pow_le_pow_left₀ (norm_nonneg _)
          ((norm_map_traceFunction_le h n y).trans (by gcongr; exact_mod_cast hN _)) 2
    _ = Fintype.card ((V ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ n)) * ((N : ℝ) * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n) ^ 2 :=
        by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (d * (Nat.card k₀ : ℝ) ^ n) * ((N : ℝ) * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ n) ^ 2 := by
        gcongr
    _ = ((d : ℝ) * (N : ℝ) ^ 2) * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * (w + 1)) := by
        rw [mul_pow, ← pow_mul, ← Real.rpow_natCast _ (n * 2), ← Real.rpow_mul hq.le,
          ← Real.rpow_natCast (Nat.card k₀ : ℝ) n, show (n : ℝ) * (w + 1) = n + (w / 2 * ↑(n * 2))
            by push_cast; ring, Real.rpow_add hq]
        ring

/-- The `L²`-weight is at most the weight: if `F` is a lisse Weil sheaf on the smooth
geometrically connected affine curve `V`, punctually `ι`-mixed of weights at most `w`, then
`‖F‖ ≤ w`, by `AlgebraicGeometry.WeilSheaf.exists_traceEnergy_le_of_hasWeightsAtMost` and
`AlgebraicGeometry.WeilSheaf.l2Weight_le_of_traceEnergy_le`. (blueprint:
`lemma-bounds-squared-traces--2`) -/
theorem l2Weight_le_of_hasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l V) (hlisse : F.IsLisse) {w : ℝ} (h : F.HasWeightsAtMost ι w) :
    F.l2Weight ι ≤ w := by
  obtain ⟨C, hC⟩ := exists_traceEnergy_le_of_hasWeightsAtMost ι F hlisse h
  simpa using F.l2Weight_le_of_traceEnergy_le ι hC

/-- Let `F` be a lisse Weil sheaf on the smooth geometrically connected affine curve `X₀` and
`F'` a Weil sheaf whose local eigenvalues are the complex conjugates of those of `F` (the sheaf
`F̄` of the complex-conjugate local Frobenius eigenvalues), in that the local polynomials of
`F'` are the conjugates of those of `F` under `ι`. Then at every `y ∈ X₀(𝔽_{qᵐ})`

`ι Tr(F_y | (F ⊗ F̄)_ȳ) = |ι Tr(F_y | F_ȳ)|² ≥ 0`,

and consequently the `L²`-series `φ_F(t) = ∑_{m ≥ 1} S_m t^{m - 1}` is the logarithmic
derivative `L'/L` of the `L`-series `L(X₀, F ⊗ F̄, t)`
(`AlgebraicGeometry.WeilSheaf.lSeries`), the Euler-product form of the Grothendieck–Lefschetz
trace formula: `φ_F · L = L'`. (blueprint: `theorem-weights-sums-squared-traces`) -/
theorem traceFunction_tensorObj_and_l2Series_mul_lSeries (ι : PadicAlgCl l →+* ℂ)
    {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (F F' : WeilSheaf k₀ l V) (hlisse : F.IsLisse)
    (hconj : ∀ x : V.finitePoints, (F'.stalk x).localPolynomial.map ι =
      ((F.stalk x).localPolynomial.map ι).map (starRingEnd ℂ)) :
    (∀ (n : ℕ) (y : (V ↘ Spec (CommRingCat.of k₀)).fieldPoints
        (FiniteField.galoisExtension k₀ n)),
      ι ((F.tensorObj F' hlisse).traceFunction n y) = ((‖ι (F.traceFunction n y)‖ ^ 2 : ℝ) : ℂ)) ∧
    PowerSeries.mk (fun m ↦ (F.traceEnergy ι (m + 1) : ℂ)) * (F.tensorObj F' hlisse).lSeries ι =
      PowerSeries.derivative (R := ℂ) ((F.tensorObj F' hlisse).lSeries ι) := by
  have : QuasiCompact (V ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have hy (n : ℕ) (y : (V ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
      ι ((F.tensorObj F' hlisse).traceFunction n y) =
        ((‖ι (F.traceFunction n y)‖ ^ 2 : ℝ) : ℂ) := by
    rw [traceFunction_tensorObj, map_mul, traceFunction_eq_trace F', traceFunction_eq_trace F,
      FrobeniusModule.map_trace_frobeniusEnd_pow_eq_of_map_localPolynomial_eq
        (F.stalk (finitePointOfFieldPoint y)) (F'.stalk (finitePointOfFieldPoint y)) ι
        ((starRingEnd ℂ).comp ι) (by rw [hconj, Polynomial.map_map]), RingHom.comp_apply,
      Complex.conj_mul']
    push_cast
    rfl
  refine ⟨hy, ?_⟩
  set L := (F.tensorObj F' hlisse).lSeries ι
  have h := (F.tensorObj F' hlisse).X_mul_derivative_lSeries ι
  have hA : PowerSeries.mk (fun n ↦ if n = 0 then 0 else
      ∑ᶠ y, ι ((F.tensorObj F' hlisse).traceFunction n y)) =
      PowerSeries.X * PowerSeries.mk (fun m ↦ (F.traceEnergy ι (m + 1) : ℂ)) := by
    ext n
    rcases n with _ | n
    · simp
    rw [PowerSeries.coeff_mk, ite_eq_right n.succ_ne_zero, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, traceEnergy]
    have : Finite (FiniteField.galoisExtension k₀ (n + 1)) := Module.finite_of_finite k₀
    have := (V ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints
      (FiniteField.galoisExtension k₀ (n + 1))
    let : Fintype ((V ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ (n + 1))) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun y _ ↦ hy _ y
  rw [hA, mul_assoc] at h
  exact (mul_left_cancel₀ PowerSeries.X_ne_zero h).symm

/-- The *`L²`-rigidity* for real sheaves: let `G` be a nonzero lisse `ι`-real Weil sheaf on the
smooth geometrically connected affine curve `X₀`, punctually `ι`-pure of weight `w`. Then
`‖G‖ = w`.

The proof in the blueprint writes `φ_G = L'/L` with `L` the ratio of the determinants of the
Frobenius on `H_c¹` and `H_c²` of `G ⊗ G`; the denominator is pure of weight `2w + 2` by the
endpoint lemma, positivity of the local factors forces a surviving pole on `|t| = q^{-w-1}`,
and the radius `q^{-w-1}` gives `‖G‖ = w` by `AlgebraicGeometry.WeilSheaf.lt_l2Weight_iff`.
(blueprint: `theorem-weights-sums-squared-traces`) -/
theorem l2Weight_eq_of_isReal (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l V) (hG : ¬ Limits.IsZero G) (hlisse : G.IsLisse) (hreal : G.IsReal ι)
    {w : ℝ} (hpure : G.IsPunctuallyPureOfWeight ι w) :
    G.l2Weight ι = w := by
  have : QuasiCompact (V ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  set T := G.tensorObj G hlisse
  have hTl : T.IsLisse := hlisse.tensorObj hlisse
  have hTp : T.IsPunctuallyPureOfWeight ι (w + w) := hpure.tensorObj hlisse hpure
  -- `φ_G = L'/L` for the `L`-series of `G ⊗ G`
  have hconj : ∀ x : V.finitePoints, (G.stalk x).localPolynomial.map ι =
      ((G.stalk x).localPolynomial.map ι).map (starRingEnd ℂ) := fun x ↦ by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map, hreal x n]
  have hφL := (traceFunction_tensorObj_and_l2Series_mul_lSeries ι G G hlisse hconj).2
  have hrad1 : (G.l2Series ι).radius ≤ (T.lSeries ι).radius := by
    rw [l2Series, FormalMultilinearSeries.radius_ofScalars_real_eq]
    exact PowerSeries.radius_le_radius_of_derivative_eq_mul hφL.symm
  -- the `L`-series is not a polynomial: it dominates a local factor of positive degree
  have hLtop : (T.lSeries ι).radius ≠ ⊤ := by
    obtain ⟨x, hx⟩ := G.exists_nontrivial_stalk_of_not_isZero hG
    have hle := PowerSeries.radius_tprod_le_radius
      (hreal.hasNonnegCoeffs_lFactor_tensorObj hlisse) (constantCoeff_lFactor ι T)
      (multipliable_lFactor ι T) x
    set d := (V ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
    set Q : Polynomial ℂ := ((T.stalk x).localPolynomial.map ι).comp (Polynomial.X ^ d)
    have hd : d ≠ 0 := (V ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
    have hrank : Module.finrank (PadicAlgCl l) (T.stalk x).carrier ≠ 0 := by
      have e₁ : (T.stalk x).carrier ≃ₗ[PadicAlgCl l]
          (((G.dual hlisse).stalk x).carrier →ₗ[PadicAlgCl l] (G.stalk x).carrier) :=
        stalkAtTensorObjLinearEquiv _ _ _ hlisse G
      have e₂ : ((G.dual hlisse).stalk x).carrier ≃ₗ[PadicAlgCl l]
          Module.Dual (PadicAlgCl l) (G.stalk x).carrier :=
        (stalkAtDualEquiv _ _ _ G hlisse).toLinearEquiv
      rw [e₁.finrank_eq, Module.finrank_linearMap, e₂.finrank_eq, Subspace.dual_finrank_eq]
      exact mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'
    have hQdeg : Q.degree ≠ 0 := by
      refine fun h0 ↦ mul_ne_zero ?_ (by simpa using hd)
        (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h0.le |>
          (Polynomial.natDegree_comp.symm.trans ·))
      rw [Polynomial.natDegree_map, FrobeniusModule.natDegree_localPolynomial]
      exact hrank
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q hQdeg
    have hQ0 : Q.coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
        Polynomial.eval_X, zero_pow hd, ← Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_map, FrobeniusModule.coeff_zero_localPolynomial, map_one]
      exact one_ne_zero
    have hzr : (T.lFactor ι x).radius ≤ ‖z‖₊ := by
      by_contra h
      exact PowerSeries.eval_ne_zero_of_lt_radius_inv hQ0 (not_le.1 h) hz.eq_zero
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hle.trans hzr)
  -- the denominator `det(1 - Ft | H_c²)` has its zeros on `|t| = q^{-w-1}`
  set R : ℝ := (Nat.card k₀ : ℝ) ^ (-(w + 1))
  have h2 : (T.compactlySupportedCohomology 2).IsPureOfWeight ι (Nat.card k₀) (w + w + 2) :=
    FrobeniusModule.IsPureOfWeight.of_equiv
      (compactlySupportedCohomologyEquivOfIso ((lowerStarIdIso k₀ l V).app T).symm 2)
      (isPureOfWeightOver_compactlySupportedCohomology_directImage_two (𝟙 V) T ι hTl hTp)
  have hD : ((T.compactlySupportedCohomology 2).localPolynomial.map ι) ≠ 0 := fun h0 ↦ by
    have := congrArg (Polynomial.coeff · 0) h0
    simp [FrobeniusModule.coeff_zero_localPolynomial] at this
  have hroots : ∀ z : ℂ, ((T.compactlySupportedCohomology 2).localPolynomial.map ι).eval z = 0 →
      ‖z‖₊ ≤ R.toNNReal := fun z hz ↦ by
    rw [← NNReal.coe_le_coe, coe_nnnorm, h2.norm_eq_of_eval_map_localPolynomial_eq_zero hz,
      Real.coe_toNNReal _ (by positivity)]
    exact le_of_eq (by congr 1; ring)
  have hLR : (T.lSeries ι).radius ≤ ENNReal.ofReal R :=
    PowerSeries.radius_le_of_mul_coe_eq
      (lSeries_mul_localPolynomial_compactlySupportedCohomology_two ι T hTl) hD hroots hLtop
  -- conclusion
  refine le_antisymm (l2Weight_le_of_hasWeightsAtMost ι G hlisse hpure.hasWeightsAtMost) ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨β, hβ1, hβ2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hβw : β < w := EReal.coe_lt_coe_iff.1 hβ2
  have hβ := (lt_l2Weight_iff ι G β).2 ((hrad1.trans hLR).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (Real.rpow_lt_rpow_of_exponent_lt hq (by linarith))))
  exact hβ1.not_gt hβ

/-- The *`L²`-weight of a punctually pure lisse sheaf equals its weight*: let `G` be a nonzero
lisse Weil sheaf on the smooth geometrically connected affine curve `X₀`, punctually `ι`-pure
of weight `w`. Then `‖G‖ = w`; the reality hypothesis of
`AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isReal` is not needed.

The twist `G⁰ = G ⊗ 𝓑_b` with `|ι b| = q^{-w/2}` has `‖G⁰‖ = ‖G‖ - w`; its envelope `E` is
real and pure of weight `0`, so `‖E‖ = 0`; the traces of `E` are `2 Re t_{G⁰}`, so
`‖E‖ ≤ ‖G⁰‖`; and `‖G⁰‖ ≤ 0` by `AlgebraicGeometry.WeilSheaf.l2Weight_le_of_hasWeightsAtMost`.
(blueprint: `theorem-weights-sums-squared-traces--1`) -/
theorem l2Weight_eq_of_isPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l V) (hG : ¬ Limits.IsZero G) (hlisse : G.IsLisse) {w : ℝ}
    (hpure : G.IsPunctuallyPureOfWeight ι w) :
    G.l2Weight ι = w := by
  obtain ⟨b, hb⟩ := G.exists_norm_eq_of_isPunctuallyPureOfWeight ι hG hpure
  have hq : 1 < (Nat.card k₀ : ℝ) := by exact_mod_cast Finite.one_lt_card
  have hc : 2 * Real.logb (Nat.card k₀) ‖ι b‖ = -w := by
    rw [hb, Real.logb_rpow (by linarith) hq.ne']
    ring
  -- Step 1: the twist shifts the `L²`-weight by `w`
  have h1 : (G.constantTwist b).l2Weight ι = G.l2Weight ι - w :=
    l2Weight_eq_sub_of_traceEnergy_eq ι G _ (traceEnergy_constantTwist ι G hb)
  -- Step 2: the envelope has `L²`-weight zero
  have h2 : (G.realEnvelope hlisse b).l2Weight ι = 0 := by
    exact_mod_cast l2Weight_eq_of_isReal ι _ (not_isZero_realEnvelope hG hlisse b)
      (hlisse.realEnvelope b) (isReal_realEnvelope hlisse hpure hb)
      (hpure.realEnvelope hlisse hb)
  -- Step 3: comparison with the envelope
  have h3 : (G.realEnvelope hlisse b).l2Weight ι ≤ (G.constantTwist b).l2Weight ι :=
    l2Weight_le_of_traceEnergy_le_mul ι _ _ (by norm_num)
      (traceEnergy_realEnvelope_le ι hlisse hpure hb)
  have h4 : (G.constantTwist b).l2Weight ι ≤ 0 := by
    have := l2Weight_le_of_hasWeightsAtMost ι _ (hlisse.constantTwist (b := b))
      (hpure.constantTwist hc).hasWeightsAtMost
    simpa using this
  have h0 : G.l2Weight ι - w = 0 := h1 ▸ le_antisymm h4 (h2 ▸ h3)
  have := congrArg (· + (w : EReal)) h0
  simp only [zero_add] at this
  rwa [EReal.sub_add_cancel] at this

-- the hypothesis `0 < C` is not needed for the bound
set_option linter.unusedVariables false in
/-- Let `N ≠ 0` be lisse on a smooth geometrically connected affine curve `V₀` of finite type
over `k₀` and punctually `ι`-pure of weight `v`. If the trace energies satisfy
`S_n(V₀, N) ≤ C q^{nB}` for every `n ≥ 1`, with `0 < C` independent of `n`, then `v ≤ B - 1`.

The energy bound bounds the `L²`-weight parameter `‖N‖` by `B - 1`
(`AlgebraicGeometry.WeilSheaf.l2Weight_le_of_traceEnergy_le`), and `‖N‖ = v` by the
`L²`-rigidity `AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight`. -/
theorem le_sub_one_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (N : WeilSheaf k₀ l V) (hN : ¬ Limits.IsZero N) (hlisse : N.IsLisse) {v : ℝ}
    (hpure : N.IsPunctuallyPureOfWeight ι v) {C B : ℝ} (hC : 0 < C)
    (hS : ∀ n : ℕ, 1 ≤ n → N.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B)) :
    v ≤ B - 1 := by
  have h := (l2Weight_eq_of_isPunctuallyPureOfWeight ι N hN hlisse hpure).symm.trans_le
    (N.l2Weight_le_of_traceEnergy_le ι hS)
  exact_mod_cast h

namespace LisseOnDenseOpen

/-- The boundary contribution `E_m = ∑_{y ∈ S₀(𝔽_{qᵐ})} |ι t_{j_*M}(y)|²` to the trace energy
of the direct image `j_*M`: the sum over the `𝔽_{qᵐ}`-points of the affine line outside `U₀`. -/
noncomputable def boundaryEnergy (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) (m : ℕ) :
    ℝ :=
  ∑ᶠ (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ m))
    (_ : y.1.base (IsLocalRing.closedPoint _) ∉ Set.range D.j.base),
    ‖ι (D.directImage.traceFunction m y)‖ ^ 2

/-- The boundary contribution is nonnegative, as a sum of squares. -/
theorem boundaryEnergy_nonneg (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) (m : ℕ) :
    0 ≤ D.boundaryEnergy ι m :=
  finsum_nonneg fun _ ↦ finsum_nonneg fun _ ↦ sq_nonneg _

/-- The trace function of the direct image `j_*M` at a rational point of `U₀` is that of `M`:
`j^* j_* M ≅ M`. -/
theorem traceFunction_directImage_mapFieldPoints (D : LisseOnDenseOpen k₀ l) (m : ℕ)
    (y : (D.U ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m)) :
    D.directImage.traceFunction m (D.j.mapFieldPoints _ y) = D.sheaf.traceFunction m y := by
  have h : D.directImage = (WeilSheaf.lowerStar D.j).obj D.sheaf := rfl
  rw [h, ← traceFunction_upperStar]
  exact traceFunction_eq_of_iso (upperStarDirectImageIso D.j D.sheaf) m y

/-- The rational points of the affine line whose closed point lies in `U₀` are the images of the
rational points of `U₀`. -/
theorem mem_range_mapFieldPoints_iff (D : LisseOnDenseOpen k₀ l) (m : ℕ)
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ m)) :
    y ∈ Set.range (D.j.mapFieldPoints (k₀ := k₀) (K := FiniteField.galoisExtension k₀ m)) ↔
      y.1.base (IsLocalRing.closedPoint _) ∈ Set.range D.j.base := by
  constructor
  · rintro ⟨y', rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨u, hu⟩
    have hr : Set.range y.1.base ⊆ Set.range D.j.base := by
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]
      exact ⟨u, hu⟩
    refine ⟨⟨IsOpenImmersion.lift D.j y.1 hr, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    rw [← comp_over D.j (Spec (CommRingCat.of k₀)), ← Category.assoc,
      IsOpenImmersion.lift_fac]
    exact y.2

lemma injective_mapFieldPoints (D : LisseOnDenseOpen k₀ l) (m : ℕ) :
    Function.Injective (D.j.mapFieldPoints (k₀ := k₀) (K := FiniteField.galoisExtension k₀ m)) :=
  fun _ _ h ↦ Subtype.ext ((cancel_mono D.j).1 (congrArg Subtype.val h))

/-- The trace energy of the direct image `j_*M` is that of `M` plus the boundary contribution
`E_m`: since `j^*j_*M ≅ M`, the trace functions of `j_*M` and `M` agree at the points of `U₀`.
(blueprint: `corollary-sums-squared-traces-j-shriek--2`) -/
theorem traceEnergy_directImage_eq_add (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l)
    (m : ℕ) :
    D.directImage.traceEnergy ι m = D.sheaf.traceEnergy ι m + D.boundaryEnergy ι m := by
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  have := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints
    (FiniteField.galoisExtension k₀ m)
  set s := Set.range (D.j.mapFieldPoints (k₀ := k₀) (K := FiniteField.galoisExtension k₀ m))
  rw [traceEnergy, ← finsum_mem_univ, ← Set.union_compl_self s,
    finsum_mem_union disjoint_compl_right.symm.symm (Set.toFinite _) (Set.toFinite _),
    finsum_mem_range (injective_mapFieldPoints D m)]
  congr 1
  · exact finsum_congr fun y ↦ by rw [traceFunction_directImage_mapFieldPoints]
  · rw [boundaryEnergy]
    refine finsum_congr fun y ↦ ?_
    rw [Set.mem_compl_iff, mem_range_mapFieldPoints_iff]

/-- The boundary contribution `E_m` is at most `C q^{mw}` when `M` has weights at most `w`.
(blueprint: `corollary-sums-squared-traces-j-shriek--2`) -/
theorem exists_boundaryEnergy_le (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) {w : ℝ}
    (h : D.sheaf.HasWeightsAtMost ι w) :
    ∃ C : ℝ, ∀ m : ℕ, D.boundaryEnergy ι m ≤ C * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) := by
  classical
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : GeometricallyConnected (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  -- boundary semicontinuity: `j_*M` has weights at most `w` everywhere
  have hJ : D.directImage.HasWeightsAtMost ι w :=
    WeilSheaf.hasWeightsAtMost_directImage D.j ι D.lisse h
  -- the boundary is a finite set of closed points
  have : Nonempty (affineLine k₀) :=
    ⟨(AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀))) 0).base (IsLocalRing.closedPoint k₀)⟩
  have hU : (Set.range D.j.base).Nonempty := by
    have : Nonempty D.U := D.j.denseRange.nonempty_iff.2 ‹_›
    exact Set.range_nonempty _
  have := LocallyOfFiniteType.isLocallyNoetherian (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian (affineLine k₀) := ⟨⟩
  have hfin : (Set.range D.j.base)ᶜ.Finite :=
    D.j.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one
      (topologicalKrullDim_le_of_smoothOfRelativeDimension
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) 1) hU
  let B : Finset (affineLine k₀).finitePoints :=
    (hfin.preimage Subtype.val_injective.injOn).toFinset
  have hB (x : (affineLine k₀).finitePoints) : x ∈ B ↔ x.1 ∉ Set.range D.j.base := by
    simp [B]
  let N : ℕ := B.sup fun x ↦ Module.finrank (PadicAlgCl l) (D.directImage.stalk x).carrier
  let d : ℕ := ∑ x ∈ B, (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  refine ⟨d * N ^ 2, fun m ↦ ?_⟩
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  have := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints
    (FiniteField.galoisExtension k₀ m)
  set s := {y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ m) | y.1.base (IsLocalRing.closedPoint _) ∉ Set.range D.j.base}
  have hs : s.Finite := Set.toFinite s
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  -- each boundary term is at most `N² q^{mw}`
  have hterm (y) (hy : y ∈ s) : ‖ι (D.directImage.traceFunction m y)‖ ^ 2 ≤
      (N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) := by
    have hb := norm_map_traceFunction_le hJ m y
    have hN : Module.finrank (PadicAlgCl l)
        (D.directImage.stalk (finitePointOfFieldPoint y)).carrier
        ≤ N := Finset.le_sup (f := fun x ↦ Module.finrank (PadicAlgCl l)
          (D.directImage.stalk x).carrier) ((hB _).2 hy)
    have hpow : ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ m * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ m =
        (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) := by
      rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hq]
      congr 1
      push_cast
      ring
    have h0 : (0 : ℝ) ≤ ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ m := by positivity
    calc ‖ι (D.directImage.traceFunction m y)‖ ^ 2
        ≤ ((N : ℝ) * ((Nat.card k₀ : ℝ) ^ (w / 2)) ^ m) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb.trans (by gcongr)) 2
      _ = _ := by rw [mul_pow, sq (((Nat.card k₀ : ℝ) ^ (w / 2)) ^ m), hpow]
  -- there are at most `d` boundary points
  have hcard : hs.toFinset.card ≤ d := by
    rw [Finset.card_eq_sum_card_fiberwise (f := finitePointOfFieldPoint) (t := B)
      (fun y hy ↦ (hB _).2 (hs.mem_toFinset.1 hy))]
    refine Finset.sum_le_sum fun x hx ↦ ?_
    calc _ ≤ Nat.card {p : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ m) // p.1.base (IsLocalRing.closedPoint _) = x.1} := by
          rw [← Nat.card_eq_finsetCard]
          refine Nat.card_le_card_of_injective (fun p ↦ ⟨p.1, congrArg Subtype.val
            (Finset.mem_filter.1 p.2).2⟩) fun p p' h ↦
              Subtype.ext (by simpa using congrArg Subtype.val h)
      _ ≤ _ := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).card_fieldPoints_base_eq_le _ x.2
  rw [boundaryEnergy]
  change ∑ᶠ y ∈ s, _ ≤ _
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]
  calc ∑ y ∈ hs.toFinset, ‖ι (D.directImage.traceFunction m y)‖ ^ 2
      ≤ ∑ _y ∈ hs.toFinset, (N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) :=
        Finset.sum_le_sum fun y hy ↦ hterm y (hs.mem_toFinset.1 hy)
    _ = hs.toFinset.card * ((N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d * ((N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w)) := by
        gcongr
    _ = _ := by ring

/-- The trace energies of the lisse sheaf `M` on the dense open `U₀` are at most those of its
direct image `j_*M` on the affine line, the boundary contribution being nonnegative. -/
theorem traceEnergy_le_traceEnergy_directImage (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) (m : ℕ) :
    D.sheaf.traceEnergy ι m ≤ D.directImage.traceEnergy ι m := by
  rw [traceEnergy_directImage_eq_add]
  exact le_add_of_nonneg_right (D.boundaryEnergy_nonneg ι m)

/-- The trace energies of the direct image `j_*M` exceed those of `M` by at most `C q^{mw}` when
`M` has weights at most `w`. -/
theorem exists_traceEnergy_directImage_le_add (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) {w : ℝ} (h : D.sheaf.HasWeightsAtMost ι w) :
    ∃ C : ℝ, ∀ m : ℕ, D.directImage.traceEnergy ι m ≤
      D.sheaf.traceEnergy ι m + C * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) := by
  obtain ⟨C, hC⟩ := D.exists_boundaryEnergy_le ι h
  exact ⟨C, fun m ↦ (traceEnergy_directImage_eq_add ι D m).trans_le
    ((add_le_add_iff_left _).2 (hC m))⟩

/-- *The middle extension does not change the `L²`-weight*: let `j : U₀ ↪ 𝔸¹_{k₀}` be a dense
open immersion and `M` a nonzero lisse Weil sheaf on the smooth geometrically connected affine
curve `U₀`, punctually `ι`-pure of weight `w`. Then `‖j_*M‖ = ‖M‖ = w`.

The rigidity `AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight` gives
`‖M‖ = w`. The trace energies of `j_*M` are those of `M` plus the boundary contribution
`E_m = ∑_{y ∈ S₀(𝔽_{qᵐ})} |t_{j_*M}(y)|² ≥ 0`, which is at most `D r² q^{mw}` by the boundary
semicontinuity, with `D = ∑_{s ∈ S₀} d(s)` and `r` the rank of `M`. Hence `‖M‖ ≤ ‖j_*M‖` and
`‖j_*M‖ ≤ max ‖M‖ (w - 1) = w`.

The nonvanishing of `M`, implicit in the blueprint, is needed: the zero sheaf has `‖0‖ = -∞`.
(blueprint: `corollary-sums-squared-traces-j-shriek--2`) -/
theorem l2Weight_directImage (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l)
    [IsAffine D.U] [LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (D.U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (D.U ↘ Spec (CommRingCat.of k₀))]
    (hM : ¬ Limits.IsZero D.sheaf) {w : ℝ} (hpure : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    D.directImage.l2Weight ι = D.sheaf.l2Weight ι ∧ D.sheaf.l2Weight ι = w := by
  have hw := l2Weight_eq_of_isPunctuallyPureOfWeight ι D.sheaf hM D.lisse hpure
  have hle : D.sheaf.l2Weight ι ≤ D.directImage.l2Weight ι :=
    l2Weight_le_l2Weight_of_traceEnergy_le ι _ _ (traceEnergy_le_traceEnergy_directImage ι D)
  obtain ⟨C, hC⟩ := exists_traceEnergy_directImage_le_add ι D hpure.hasWeightsAtMost
  have hge : D.directImage.l2Weight ι ≤ max (D.sheaf.l2Weight ι) ((w - 1 : ℝ) : EReal) :=
    l2Weight_le_max_of_traceEnergy_le_add ι _ _ hC
  rw [hw, max_eq_left (EReal.coe_le_coe_iff.2 (by linarith))] at hge
  exact ⟨le_antisymm (hge.trans_eq hw.symm) hle, hw⟩

end LisseOnDenseOpen

end WeilSheaf

end AlgebraicGeometry
