import Langlands.Theta.Metaplectic.StandardOperator
import Langlands.Theta.Metaplectic.SiegelLevi

/-!
# The standard Weil operator on the Siegel parabolic subgroup

GKT §2.3.2 (the Siegel parabolic `P(X)`, `m(a)`, `n(b)`, p. 57; **Lemma 2.16**, p. 58;
**Proposition 2.17** and **Corollary 2.18**, pp. 59–60; Corollary 2.21, p. 60). For a pairing `β`,
the Lagrangian of the Schrödinger model of `polarizedForm β` is `0 × Y` (the book's `X`).

* `siegelParabolicGroup β`: the isometries `p` with `p (0 × Y) = 0 × Y`; it contains the Siegel
  Levi `siegelLeviGroup β` and the unipotent elements `siegelUnipotentElement β b hb`
  (`(x, y) ↦ (x, y + b x)` for `b : X → Y` with `β(x, b x')` symmetric, the book's `n(b)`).
* `standardOperator_of_mem_siegelParabolicGroup`: **Lemma 2.16**,
  `r(p) φ(x) = |det d|^{1/2} ψ(½ β(d x, b x)) φ(d x)` where `p⁻¹ (x, 0) = (d x, b x)`, and
  `standardMeasure_univ_of_mem_siegelParabolicGroup`: the measure `d_p` of the point `Y ⧸ Y` is
  `|det d|^{1/2}`.
* `standardOperator_mul_of_mem_left`, `standardOperator_mul_of_mem_right`:
  **Proposition 2.17**, `r(p g) = r(p) r(g)` and `r(g p) = r(g) r(p)`, with the measures carried
  along (an isomorphism of the quotients `Y ⧸ ker c` multiplies Haar measures by a positive
  constant, which unitarity forces to be the right one).
* `siegelParabolicSplitting`: **Corollary 2.18**, `p ↦ (p, r(p))` is a splitting of `P(X)`;
  `standardOperator_siegelLevi`: on the Levi it is `siegelLeviWeil` (`Metaplectic/SiegelLevi.lean`);
  `standardOperator_siegelUnipotentElement`: `r(n(b)) φ(x) = ψ(-½ β(x, b x)) φ(x)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

section Group

variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

variable (β : X →ₗ[R] Y →ₗ[R] R) in
/-- **The Siegel parabolic subgroup** `P(X)` of the Lagrangian `X = 0 × Y` (GKT §2.3.2, p. 57):
the isometries `p` of `polarizedForm β` with `p (0 × Y) = 0 × Y`. -/
def siegelParabolicGroup : Subgroup (isometryGroup (polarizedForm β)) where
  carrier := {p | ∀ y : Y, ((p : (X × Y) ≃ₗ[R] X × Y) (0, y)).1 = 0 ∧ (isometryInv p (0, y)).1 = 0}
  mul_mem' {p q} hp hq y := by
    have hq1 := (hq y).1
    have hp1 := (hp ((q : (X × Y) ≃ₗ[R] X × Y) (0, y)).2).1
    have hp2 := (hp y).2
    have hq2 := (hq (isometryInv p (0, y)).2).2
    refine ⟨?_, ?_⟩
    · change ((p : (X × Y) ≃ₗ[R] X × Y) ((q : (X × Y) ≃ₗ[R] X × Y) (0, y))).1 = 0
      rw [show (q : (X × Y) ≃ₗ[R] X × Y) (0, y) = (0, ((q : (X × Y) ≃ₗ[R] X × Y) (0, y)).2) from
        Prod.ext hq1 rfl]
      exact hp1
    · change (isometryInv q (isometryInv p (0, y))).1 = 0
      rw [show isometryInv p (0, y) = (0, (isometryInv p (0, y)).2) from Prod.ext hp2 rfl]
      exact hq2
  one_mem' y := ⟨rfl, rfl⟩
  inv_mem' {p} hp y := by
    refine ⟨(hp y).2, ?_⟩
    simp only [isometryInv, inv_inv]
    exact (hp y).1

theorem mem_siegelParabolicGroup {β : X →ₗ[R] Y →ₗ[R] R} {p : isometryGroup (polarizedForm β)} :
    p ∈ siegelParabolicGroup β ↔
      ∀ y : Y, ((p : (X × Y) ≃ₗ[R] X × Y) (0, y)).1 = 0 ∧ (isometryInv p (0, y)).1 = 0 :=
  Iff.rfl

variable {β : X →ₗ[R] Y →ₗ[R] R}

/-- On the Siegel parabolic the c-part of `p⁻¹` vanishes (GKT Lemma 2.16: `c(p⁻¹) = 0`). -/
theorem standardC_eq_zero_of_mem {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) : standardC p = 0 :=
  LinearMap.ext fun y => (hp y).2

/-- On the Siegel parabolic, `ker c` is everything. -/
theorem standardKernel_eq_top_of_mem {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) : standardKernel p = ⊤ := by
  rw [standardKernel, standardC_eq_zero_of_mem hp, LinearMap.ker_zero]

/-- `isometryInv p⁻¹ = p`. -/
theorem isometryInv_inv (p : isometryGroup (polarizedForm β)) :
    isometryInv p⁻¹ = (p : (X × Y) ≃ₗ[R] X × Y) := by
  rw [isometryInv, inv_inv]

/-- The d-block of `p⁻¹` for `p` in the Siegel parabolic, as an automorphism of `X` (the book's
`a^*` in `p⁻¹ = [[a⁻¹, -b a^*], [0, a^*]]`, proof of Lemma 2.16). -/
def siegelD {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    X ≃ₗ[R] X where
  toLinearMap := standardD p
  invFun := standardD p⁻¹
  left_inv x := by
    change (isometryInv p⁻¹ ((isometryInv p (x, 0)).1, 0)).1 = x
    rw [isometryInv_inv]
    have h1 := (hp (isometryInv p (x, 0)).2).1
    have e : ((isometryInv p (x, 0)).1, (0 : Y)) =
        isometryInv p (x, 0) - (0, (isometryInv p (x, 0)).2) := by ext <;> simp
    rw [e, map_sub, Prod.fst_sub, h1, sub_zero]
    change (((p * p⁻¹ : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[R] X × Y) (x, 0)).1 = x
    rw [mul_inv_cancel]; rfl
  right_inv x := by
    change (isometryInv p ((isometryInv p⁻¹ (x, 0)).1, 0)).1 = x
    rw [isometryInv_inv]
    have h1 := (hp ((p : (X × Y) ≃ₗ[R] X × Y) (x, 0)).2).2
    have e : (((p : (X × Y) ≃ₗ[R] X × Y) (x, 0)).1, (0 : Y)) =
        (p : (X × Y) ≃ₗ[R] X × Y) (x, 0) - (0, ((p : (X × Y) ≃ₗ[R] X × Y) (x, 0)).2) := by
      ext <;> simp
    rw [e, map_sub, Prod.fst_sub, h1, sub_zero]
    change (((p⁻¹ * p : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[R] X × Y) (x, 0)).1 = x
    rw [inv_mul_cancel]; rfl

@[simp] theorem siegelD_apply {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) (x : X) : siegelD hp x = standardD p x := rfl

/-- The a-block of `p⁻¹` for `p` in the Siegel parabolic, as an automorphism of `Y`. -/
def siegelA {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    Y ≃ₗ[R] Y where
  toLinearMap := standardA p
  invFun := standardA p⁻¹
  left_inv y := by
    change (isometryInv p⁻¹ (0, (isometryInv p (0, y)).2)).2 = y
    rw [isometryInv_inv]
    have e : ((0 : X), (isometryInv p (0, y)).2) = isometryInv p (0, y) := by
      ext
      · exact ((hp y).2).symm
      · rfl
    rw [e]
    change (((p * p⁻¹ : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[R] X × Y) (0, y)).2 = y
    rw [mul_inv_cancel]; rfl
  right_inv y := by
    change (isometryInv p (0, (isometryInv p⁻¹ (0, y)).2)).2 = y
    rw [isometryInv_inv]
    have e : ((0 : X), ((p : (X × Y) ≃ₗ[R] X × Y) (0, y)).2) =
        (p : (X × Y) ≃ₗ[R] X × Y) (0, y) := by
      ext
      · exact ((hp y).1).symm
      · rfl
    rw [e]
    change (((p⁻¹ * p : isometryGroup (polarizedForm β)) : (X × Y) ≃ₗ[R] X × Y) (0, y)).2 = y
    rw [inv_mul_cancel]; rfl

@[simp] theorem siegelA_apply {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) (y : Y) : siegelA hp y = standardA p y := rfl

/-- On the Siegel parabolic `β(d x, a y) = β(x, y)` (the book's `⟨a x, y⟩ = ⟨x, a^* y⟩`,
(2.19)). -/
theorem pairing_standardD_standardA_of_mem {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) (x : X) (y : Y) :
    β (standardD p x) (standardA p y) = β x y := by
  have h := pairing_standardD_standardA p x y
  rwa [standardC_eq_zero_of_mem hp, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
    sub_zero] at h

/-- The Siegel Levi lies in the Siegel parabolic. -/
theorem siegelLeviGroup.toIsometry_mem (m : siegelLeviGroup β) :
    siegelLeviGroup.toIsometry β m ∈ siegelParabolicGroup β :=
  fun _ => ⟨by simp [siegelLeviGroup.toIsometry_apply], by
    rw [isometryInv, ← map_inv, siegelLeviGroup.toIsometry_apply]
    exact map_zero _⟩

variable (β) in
/-- **The unipotent element `n(b)`** of the Siegel parabolic (GKT p. 57): `(x, y) ↦ (x, y + b x)`
for `b : X → Y` with `β(x, b x') = β(x', b x)` (the book's symmetry (2.20)). -/
def siegelUnipotentElement (b : X →ₗ[R] Y) (hb : ∀ x x', β x (b x') = β x' (b x)) :
    isometryGroup (polarizedForm β) :=
  ⟨{ toFun := fun w => (w.1, w.2 + b w.1)
     map_add' := fun w w' => by ext <;> simp [add_add_add_comm]
     map_smul' := fun c w => by ext <;> simp [smul_add]
     invFun := fun w => (w.1, w.2 - b w.1)
     left_inv := fun w => by ext <;> simp
     right_inv := fun w => by ext <;> simp },
   fun w w' => by
     change polarizedForm β (w.1, w.2 + b w.1) (w'.1, w'.2 + b w'.1) = polarizedForm β w w'
     simp only [polarizedForm_apply, map_add]
     rw [hb w.1 w'.1]
     ring⟩

theorem siegelUnipotentElement_apply (b : X →ₗ[R] Y) (hb : ∀ x x', β x (b x') = β x' (b x))
    (w : X × Y) :
    (siegelUnipotentElement β b hb : (X × Y) ≃ₗ[R] X × Y) w = (w.1, w.2 + b w.1) := rfl

theorem isometryInv_siegelUnipotentElement (b : X →ₗ[R] Y) (hb : ∀ x x', β x (b x') = β x' (b x))
    (w : X × Y) : isometryInv (siegelUnipotentElement β b hb) w = (w.1, w.2 - b w.1) := rfl

theorem siegelUnipotentElement_mem (b : X →ₗ[R] Y) (hb : ∀ x x', β x (b x') = β x' (b x)) :
    siegelUnipotentElement β b hb ∈ siegelParabolicGroup β :=
  fun _ => ⟨rfl, rfl⟩

end Group

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X] [FiniteDimensional F Y]
  [TopologicalSpace Y] [IsModuleTopology F Y] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y] [BorelSpace Y] in
/-- On the Siegel parabolic the integrand does not depend on `y`. -/
theorem standardIntegrand_of_mem {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) (φ : X → ℂ) (x : X) (y : Y) :
    standardIntegrand ψ p φ x y =
      ψ (⅟2 * β (standardD p x) (standardB p x)) * φ (standardD p x) := by
  rw [standardIntegrand_eq, standardC_eq_zero_of_mem hp]
  simp

omit [MeasurableSpace X] [BorelSpace X] in
/-- On the Siegel parabolic the standard operator for `μ` is `μ(Y ⧸ Y) ψ(½ β(d x, b x)) φ(d x)`. -/
theorem standardOperatorWith_apply_of_mem [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β)
    (μ : Measure (Y ⧸ standardKernel p)) [μ.IsAddHaarMeasure] (φ : SchwartzBruhat X) (x : X) :
    (standardOperatorWith hψ hψ1 p μ φ : X → ℂ) x =
      (μ.real Set.univ : ℂ) * (ψ (⅟2 * β (standardD p x) (standardB p x)) * φ (standardD p x)) := by
  have h : standardIntegrandQ ψ p φ x =
      fun _ => ψ (⅟2 * β (standardD p x) (standardB p x)) * φ (standardD p x) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    rw [standardIntegrandQ_mk, standardIntegrand_of_mem hp]
  rw [standardOperatorWith_apply, h, integral_const, Complex.real_smul]

omit [Invertible (2 : F)] [IsTopologicalAddGroup X] [FiniteDimensional F Y] [MeasurableSpace Y]
  [BorelSpace Y] in
/-- `∫ f(d x) dν = |det d|⁻¹ ∫ f dν` for a linear automorphism `d` and a Haar measure `ν`. -/
theorem integral_comp_linearEquiv (ν : Measure X) [ν.IsAddHaarMeasure]
    (d : X ≃ₗ[F] X) (f : X → ℂ) :
    ∫ x, f (d x) ∂ν = ((distribHaarChar F (LinearEquiv.det d))⁻¹ : ℝ≥0) • ∫ x, f x ∂ν := by
  let E := (linearEquivToContinuousAddEquiv d).toHomeomorph.toMeasurableEquiv
  have h1 : ∫ x, f (d x) ∂ν = ∫ y, f y ∂(ν.map E) := (integral_map_equiv E f).symm
  have h2 : ν.map E = ν.map d := rfl
  rw [h1, h2, map_linearEquiv_addHaar, integral_smul_nnreal_measure]

variable [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)] [FiniteDimensional F X]
  [IsModuleTopology F X] [β.IsPerfPair] [FiniteDimensional F Y] [IsModuleTopology F Y]
  [MeasurableSpace Y] [BorelSpace Y] in
/-- A non-zero Schwartz–Bruhat function (the indicator of a compact open subgroup). -/
theorem exists_schwartzBruhatInner_ne_zero [CompactOpenExhaustion X] (ν : Measure X)
    [ν.IsAddHaarMeasure] : ∃ e : SchwartzBruhat X, schwartzBruhatInner ν e e ≠ 0 := by
  obtain ⟨L, hLc, hLo, -⟩ := CompactOpenExhaustion.exists_subset (X := X) Set.univ univ_mem
  refine ⟨⟨_, HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule L hLc hLo⟩, ?_⟩
  rw [schwartzBruhatInner_self_eq_integral, Complex.ofReal_ne_zero]
  refine (integral_norm_sq_pos _ _ (x := 0) ?_).ne'
  change (L : Set X).indicator (fun _ => (1 : ℂ)) 0 ≠ 0
  rw [Set.indicator_of_mem (show (0 : X) ∈ (L : Set X) from L.zero_mem)]
  exact one_ne_zero

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)] [FiniteDimensional F X]
  [IsModuleTopology F X] [β.IsPerfPair] [FiniteDimensional F Y] [IsModuleTopology F Y]
  [MeasurableSpace Y] [BorelSpace Y] in
/-- **Two positive multiples of each other that are both unitary are equal.** -/
theorem eq_of_eq_smul_of_inner [CompactOpenExhaustion X]
    {T T' : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X} {t : ℝ}
    (ht : 0 < t) (h : T = (t : ℂ) • T') (ν : Measure X) [ν.IsAddHaarMeasure]
    (hT : ∀ φ φ', schwartzBruhatInner ν (T φ) (T φ') = schwartzBruhatInner ν φ φ')
    (hT' : ∀ φ φ', schwartzBruhatInner ν (T' φ) (T' φ') = schwartzBruhatInner ν φ φ') :
    T = T' := by
  obtain ⟨e, he⟩ := exists_schwartzBruhatInner_ne_zero ν
  have h1 := hT e e
  rw [h] at h1
  simp only [LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, RingHom.id_apply,
    Complex.conj_ofReal, hT' e e] at h1
  have h2 : ((t * t : ℝ) : ℂ) * schwartzBruhatInner ν e e = 1 * schwartzBruhatInner ν e e := by
    calc ((t * t : ℝ) : ℂ) * schwartzBruhatInner ν e e
        = (t : ℂ) * ((t : ℂ) * schwartzBruhatInner ν e e) := by push_cast; ring
      _ = _ := by rw [h1, one_mul]
  have h3 : t * t = 1 := by exact_mod_cast mul_right_cancel₀ he h2
  have h4 : t = 1 := by nlinarith
  rw [h, h4, Complex.ofReal_one, one_smul]

/-- **GKT Lemma 2.16, the measure**: for `p` in the Siegel parabolic, `d_p` gives the point
`Y ⧸ Y` the mass `|det d|^{1/2}` (the book's `∫_{ker(c(p⁻¹)) \ X} d_p x = |det a|^{1/2}`). -/
theorem standardMeasure_real_univ_of_mem {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) :
    (standardMeasure hψ hψ1 p).real Set.univ =
      ((distribHaarChar F (LinearEquiv.det (siegelD hp)) : ℝ) ^ ((1 : ℝ) / 2)) := by
  have := locallyCompactSpace_of_finiteDimensional F X
  have := compactOpenExhaustion_of_finiteDimensional F X
  set κ := (standardMeasure hψ hψ1 p).real Set.univ
  set D : ℝ≥0 := distribHaarChar F (LinearEquiv.det (siegelD hp))
  have hD : (0 : ℝ) < D := NNReal.coe_pos.2 (distribHaarChar_pos)
  obtain ⟨e, he⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure X)
  have hu := standardOperator_inner hψ hψ1 p Measure.addHaar e e
  rw [schwartzBruhatInner_self_eq_integral, schwartzBruhatInner_self_eq_integral] at hu
  rw [schwartzBruhatInner_self_eq_integral, Complex.ofReal_ne_zero] at he
  have hval : ∀ x, ‖(standardOperator hψ hψ1 p e : X → ℂ) x‖ ^ 2 =
      κ ^ 2 * ‖(e : X → ℂ) (siegelD hp x)‖ ^ 2 := fun x => by
    rw [standardOperator, standardOperatorWith_apply_of_mem hψ hψ1 hp, norm_mul, norm_mul,
      SchrodingerIrreducible.Internal.norm_addChar_eq_one hψ, one_mul, Complex.norm_real,
      Real.norm_of_nonneg measureReal_nonneg, mul_pow, siegelD_apply]
  have hcomp := integral_comp_linearEquiv (Measure.addHaar : Measure X) (siegelD hp)
    (fun x => ((‖(e : X → ℂ) x‖ ^ 2 : ℝ) : ℂ))
  simp only [hval, integral_const_mul] at hu
  have hcomp' : ∫ x, ‖(e : X → ℂ) (siegelD hp x)‖ ^ 2 ∂Measure.addHaar =
      (D⁻¹ : ℝ≥0) * ∫ x, ‖(e : X → ℂ) x‖ ^ 2 ∂Measure.addHaar := by
    have := congrArg Complex.re hcomp
    simp only [integral_complex_ofReal, Complex.ofReal_re, NNReal.smul_def, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at this
    exact this
  rw [hcomp'] at hu
  have hu' : κ ^ 2 * (D : ℝ)⁻¹ * ∫ x, ‖(e : X → ℂ) x‖ ^ 2 ∂Measure.addHaar =
      1 * ∫ x, ‖(e : X → ℂ) x‖ ^ 2 ∂Measure.addHaar := by
    rw [one_mul, mul_assoc, ← NNReal.coe_inv]; exact_mod_cast hu
  have hk : κ ^ 2 = D := by
    have := mul_right_cancel₀ he hu'
    field_simp at this
    linarith
  have hκ : 0 ≤ κ := measureReal_nonneg
  rw [← hk, ← Real.sqrt_eq_rpow, Real.sqrt_sq hκ]

/-- **GKT Lemma 2.16**: for `p` in the Siegel parabolic, with `p⁻¹ (x, 0) = (d x, b x)`,
`r(p) φ(x) = |det d|^{1/2} ψ(½ β(d x, b x)) φ(d x)` (the book's
`r(m(a) n(b)) φ(y) = ψ(½⟨a^* y, -b a^* y⟩) |det a|^{1/2} φ(a^* y)`, with `d = a^*`). -/
theorem standardOperator_of_mem_siegelParabolicGroup {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) (φ : SchwartzBruhat X) (x : X) :
    (standardOperator hψ hψ1 p φ : X → ℂ) x =
      (((distribHaarChar F (LinearEquiv.det (siegelD hp)) : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        (ψ (⅟2 * β (standardD p x) (standardB p x)) * φ (standardD p x)) := by
  rw [standardOperator, standardOperatorWith_apply_of_mem hψ hψ1 hp,
    standardMeasure_real_univ_of_mem hψ hψ1 hp]

omit [Invertible (2 : F)] [FiniteDimensional F X] [IsModuleTopology F X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [β.IsPerfPair] in
/-- **Change of variables between quotients**: for a linear isomorphism
`e : Y ⧸ K ≃ Y ⧸ K'` and Haar measures `μ`, `μ'`, there is `s > 0` with
`∫ G(e q + t) dμ = s ∫ G dμ'` for all `G` and `t`. -/
theorem exists_integral_quotientEquiv {K K' : Submodule F Y} (e : (Y ⧸ K) ≃ₗ[F] (Y ⧸ K'))
    (μ : Measure (Y ⧸ K)) [μ.IsAddHaarMeasure] (μ' : Measure (Y ⧸ K')) [μ'.IsAddHaarMeasure] :
    ∃ s : ℝ≥0, 0 < s ∧ ∀ (G : Y ⧸ K' → ℂ) (t : Y ⧸ K'),
      ∫ q, G (e q + t) ∂μ = (s : ℂ) * ∫ q', G q' ∂μ' := by
  obtain ⟨s, hs, hmap⟩ := exists_map_eq_smul μ μ' e
  refine ⟨s, hs, fun G t => ?_⟩
  let E := (linearEquivToContinuousAddEquiv e).toHomeomorph.toMeasurableEquiv
  have h1 : ∫ q, G (e q + t) ∂μ = ∫ q', G (q' + t) ∂(μ.map E) :=
    (integral_map_equiv E (fun q' => G (q' + t))).symm
  have h2 : μ.map E = μ.map e := rfl
  rw [h1, h2, hmap, integral_smul_nnreal_measure, integral_add_right_eq_self (μ := μ') G t,
    NNReal.smul_def, Complex.real_smul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X]
  [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [β.IsPerfPair] in
/-- `(g p)⁻¹ = p⁻¹ g⁻¹` on vectors. -/
theorem isometryInv_mul (g g' : isometryGroup (polarizedForm β)) (w : X × Y) :
    isometryInv (g * g') w = isometryInv g' (isometryInv g w) := by
  rw [isometryInv, mul_inv_rev]; rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X]
  [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [β.IsPerfPair] in
/-- `ker c(g p) = ker c(g)` for `p` in the Siegel parabolic. -/
theorem standardKernel_mul_of_mem_right (g : isometryGroup (polarizedForm β))
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    standardKernel (g * p) = standardKernel g := by
  ext y
  simp only [mem_standardKernel, isometryInv_mul]
  rw [isometryInv_apply_eq p, standardC_eq_zero_of_mem hp, LinearMap.zero_apply, add_zero]
  change siegelD hp (standardC g y) = 0 ↔ standardC g y = 0
  exact (siegelD hp).map_eq_zero_iff

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
  [FiniteDimensional F X] [TopologicalSpace X] [IsModuleTopology F X] [IsTopologicalAddGroup X]
  [FiniteDimensional F Y] [TopologicalSpace Y] [IsModuleTopology F Y] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [β.IsPerfPair] in
/-- `ker c(p g) = a⁻¹ (ker c(g))` for `p` in the Siegel parabolic: `a` maps `ker c(p g)` onto
`ker c(g)`. -/
theorem map_standardKernel_mul_of_mem_left (g : isometryGroup (polarizedForm β))
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    (standardKernel (p * g)).map ((siegelA hp : Y ≃ₗ[F] Y) : Y →ₗ[F] Y) = standardKernel g := by
  have hc : ∀ y, standardC (p * g) y = standardC g (standardA p y) := fun y => by
    rw [standardC_apply, isometryInv_mul, standardC_apply]
    congr 2
    rw [isometryInv_apply_eq p, standardC_eq_zero_of_mem hp]
    simp
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    have : standardC (p * g) y' = 0 := hy'
    rw [hc] at this
    exact this
  · intro hy
    refine ⟨(siegelA hp).symm y, ?_, (siegelA hp).apply_symm_apply y⟩
    change standardC (p * g) _ = 0
    rw [hc]
    change standardC g (siegelA hp ((siegelA hp).symm y)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hy

theorem standardMeasure_real_univ_pos {p : isometryGroup (polarizedForm β)}
    (hp : p ∈ siegelParabolicGroup β) : 0 < (standardMeasure hψ hψ1 p).real Set.univ := by
  rw [standardMeasure_real_univ_of_mem hψ hψ1 hp]
  exact Real.rpow_pos_of_pos (NNReal.coe_pos.2 distribHaarChar_pos) _

/-- `r(g p) = r(g) r(p)` up to a positive constant, before unitarity is used. -/
theorem exists_standardOperator_mul_of_mem_right (g : isometryGroup (polarizedForm β))
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    ∃ t : ℝ, 0 < t ∧ standardOperator hψ hψ1 g ∘ₗ standardOperator hψ hψ1 p =
      (t : ℂ) • standardOperator hψ hψ1 (g * p) := by
  set κ := (standardMeasure hψ hψ1 p).real Set.univ
  have hκ : 0 < κ := standardMeasure_real_univ_pos hψ hψ1 hp
  have hI : ∀ (φ : SchwartzBruhat X) (x : X) (y : Y),
      standardIntegrand ψ g (standardOperator hψ hψ1 p φ) x y =
        (κ : ℂ) * standardIntegrand ψ (g * p) φ x y := by
    intro φ x y
    set X' := (isometryInv g (x, y)).1
    set Y' := (isometryInv g (x, y)).2
    have e2 : isometryInv (g * p) (x, y) = (standardD p X', standardB p X' + standardA p Y') := by
      rw [isometryInv_mul, show isometryInv g (x, y) = (X', Y') from rfl, isometryInv_apply_eq,
        standardC_eq_zero_of_mem hp, LinearMap.zero_apply, add_zero]
    have hpa := pairing_standardD_standardA_of_mem hp X' Y'
    rw [standardIntegrand, standardIntegrand, e2, standardOperator,
      standardOperatorWith_apply_of_mem hψ hψ1 hp]
    change ψ (⅟2 * β X' Y' - ⅟2 * β x y) * ((κ : ℂ) * (ψ (⅟2 * β (standardD p X')
        (standardB p X')) * φ (standardD p X'))) = (κ : ℂ) * (ψ (⅟2 * β (standardD p X')
        (standardB p X' + standardA p Y') - ⅟2 * β x y) * φ (standardD p X'))
    have hph : ⅟2 * β X' Y' - ⅟2 * β x y + ⅟2 * β (standardD p X') (standardB p X') =
        ⅟2 * β (standardD p X') (standardB p X' + standardA p Y') - ⅟2 * β x y := by
      rw [map_add, hpa]; ring
    rw [← hph, AddChar.map_add_eq_mul]
    ring
  set e := Submodule.quotEquivOfEq (standardKernel g) (standardKernel (g * p))
    (standardKernel_mul_of_mem_right g hp).symm
  obtain ⟨s, hs, hint⟩ := exists_integral_quotientEquiv e (standardMeasure hψ hψ1 g)
    (standardMeasure hψ hψ1 (g * p))
  refine ⟨κ * s, mul_pos hκ (NNReal.coe_pos.2 hs), ?_⟩
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  have hQ : standardIntegrandQ ψ g (standardOperator hψ hψ1 p φ) x =
      fun q => (κ : ℂ) * standardIntegrandQ ψ (g * p) φ x (e q + 0) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    rw [add_zero, Submodule.quotEquivOfEq_mk, standardIntegrandQ_mk, standardIntegrandQ_mk, hI]
  change ∫ q, standardIntegrandQ ψ g (standardOperator hψ hψ1 p φ) x q
      ∂(standardMeasure hψ hψ1 g) = ((κ * s : ℝ) : ℂ) * ∫ q, standardIntegrandQ ψ (g * p) φ x q
      ∂(standardMeasure hψ hψ1 (g * p))
  rw [hQ, integral_const_mul, hint (standardIntegrandQ ψ (g * p) φ x) 0]
  push_cast
  ring

/-- **GKT Proposition 2.17, right**: `r(g p) = r(g) r(p)` for `p` in the Siegel parabolic. -/
theorem standardOperator_mul_of_mem_right (g : isometryGroup (polarizedForm β))
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    standardOperator hψ hψ1 (g * p) = standardOperator hψ hψ1 g ∘ₗ standardOperator hψ hψ1 p := by
  have := locallyCompactSpace_of_finiteDimensional F X
  have := compactOpenExhaustion_of_finiteDimensional F X
  obtain ⟨t, ht, h⟩ := exists_standardOperator_mul_of_mem_right hψ hψ1 g hp
  refine (eq_of_eq_smul_of_inner ht h Measure.addHaar (fun φ φ' => ?_)
    (standardOperator_inner hψ hψ1 _ Measure.addHaar)).symm
  rw [LinearMap.comp_apply, LinearMap.comp_apply, standardOperator_inner, standardOperator_inner]

/-- `r(p g) = r(p) r(g)` up to a positive constant, before unitarity is used. -/
theorem exists_standardOperator_mul_of_mem_left (g : isometryGroup (polarizedForm β))
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    ∃ t : ℝ, 0 < t ∧ standardOperator hψ hψ1 (p * g) =
      (t : ℂ) • (standardOperator hψ hψ1 p ∘ₗ standardOperator hψ hψ1 g) := by
  set κ := (standardMeasure hψ hψ1 p).real Set.univ
  have hκ : 0 < κ := standardMeasure_real_univ_pos hψ hψ1 hp
  have hI : ∀ (φ : X → ℂ) (x : X) (y : Y), standardIntegrand ψ (p * g) φ x y =
      ψ (⅟2 * β (standardD p x) (standardB p x)) *
        standardIntegrand ψ g φ (standardD p x) (standardB p x + standardA p y) := by
    intro φ x y
    have e2 : isometryInv (p * g) (x, y) =
        isometryInv g (standardD p x, standardB p x + standardA p y) := by
      rw [isometryInv_mul, isometryInv_apply_eq p x y, standardC_eq_zero_of_mem hp,
        LinearMap.zero_apply, add_zero]
    have hpa := pairing_standardD_standardA_of_mem hp x y
    rw [standardIntegrand, standardIntegrand, e2, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    rw [map_add, hpa]
    ring
  set e := Submodule.Quotient.equiv (standardKernel (p * g)) (standardKernel g) (siegelA hp)
    (map_standardKernel_mul_of_mem_left g hp)
  obtain ⟨s, hs, hint⟩ := exists_integral_quotientEquiv e (standardMeasure hψ hψ1 (p * g))
    (standardMeasure hψ hψ1 g)
  refine ⟨s / κ, div_pos (NNReal.coe_pos.2 hs) hκ, ?_⟩
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  have hQ : standardIntegrandQ ψ (p * g) φ x = fun q =>
      ψ (⅟2 * β (standardD p x) (standardB p x)) * standardIntegrandQ ψ g φ (standardD p x)
        (e q + Submodule.Quotient.mk (standardB p x)) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H y => ?_
    rw [standardIntegrandQ_mk, hI, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_add, standardIntegrandQ_mk]
    congr 2
    exact add_comm _ _
  change ∫ q, standardIntegrandQ ψ (p * g) φ x q ∂(standardMeasure hψ hψ1 (p * g)) =
    ((s / κ : ℝ) : ℂ) * (standardOperator hψ hψ1 p (standardOperator hψ hψ1 g φ) : X → ℂ) x
  rw [hQ, integral_const_mul, hint, standardOperator, standardOperatorWith_apply_of_mem hψ hψ1 hp]
  change _ = _ * ((κ : ℂ) * (ψ (⅟2 * β (standardD p x) (standardB p x)) *
    ∫ q, standardIntegrandQ ψ g φ (standardD p x) q ∂(standardMeasure hψ hψ1 g)))
  have hκ' : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  push_cast
  field_simp

/-- **GKT Proposition 2.17, left**: `r(p g) = r(p) r(g)` for `p` in the Siegel parabolic. -/
theorem standardOperator_mul_of_mem_left (g : isometryGroup (polarizedForm β))
    {p : isometryGroup (polarizedForm β)} (hp : p ∈ siegelParabolicGroup β) :
    standardOperator hψ hψ1 (p * g) = standardOperator hψ hψ1 p ∘ₗ standardOperator hψ hψ1 g := by
  have := locallyCompactSpace_of_finiteDimensional F X
  have := compactOpenExhaustion_of_finiteDimensional F X
  obtain ⟨t, ht, h⟩ := exists_standardOperator_mul_of_mem_left hψ hψ1 g hp
  refine eq_of_eq_smul_of_inner ht h Measure.addHaar
    (standardOperator_inner hψ hψ1 _ Measure.addHaar) (fun φ φ' => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, standardOperator_inner, standardOperator_inner]

/-- **GKT Proposition 2.17**: `r(p₁ g p₂) = r(p₁) r(g) r(p₂)` for `p₁`, `p₂` in the Siegel
parabolic. -/
theorem standardOperator_mul_mul_of_mem (g : isometryGroup (polarizedForm β))
    {p₁ p₂ : isometryGroup (polarizedForm β)} (hp₁ : p₁ ∈ siegelParabolicGroup β)
    (hp₂ : p₂ ∈ siegelParabolicGroup β) :
    standardOperator hψ hψ1 (p₁ * g * p₂) = standardOperator hψ hψ1 p₁ ∘ₗ
      standardOperator hψ hψ1 g ∘ₗ standardOperator hψ hψ1 p₂ := by
  rw [standardOperator_mul_of_mem_right hψ hψ1 _ hp₂, standardOperator_mul_of_mem_left hψ hψ1 _ hp₁,
    LinearMap.comp_assoc]

/-- `r(1) = 1`. -/
theorem standardOperator_one : standardOperator hψ hψ1 (1 : isometryGroup (polarizedForm β)) =
    LinearMap.id := by
  have h := standardOperator_mul_of_mem_right hψ hψ1 1 (siegelParabolicGroup β).one_mem
  rw [mul_one] at h
  refine LinearMap.ext fun φ =>
    (standardOperator_injective hψ hψ1 (1 : isometryGroup (polarizedForm β)) ?_).symm
  exact LinearMap.congr_fun h φ

/-- **The splitting of the Siegel parabolic** as a representation (GKT Corollary 2.18):
`p ↦ r(p)` is multiplicative on `P(X)` (Proposition 2.17). -/
def siegelParabolicWeil : Representation ℂ (siegelParabolicGroup β) (SchwartzBruhat X) where
  toFun p := standardOperator hψ hψ1 p.1
  map_one' := standardOperator_one hψ hψ1
  map_mul' p q := by
    change standardOperator hψ hψ1 (p.1 * q.1) =
      standardOperator hψ hψ1 p.1 ∘ₗ standardOperator hψ hψ1 q.1
    exact standardOperator_mul_of_mem_left hψ hψ1 q.1 p.2

@[simp] theorem siegelParabolicWeil_apply (p : siegelParabolicGroup β) :
    siegelParabolicWeil hψ hψ1 p = standardOperator hψ hψ1 p.1 := rfl

theorem siegelParabolicWeil_normalizes :
    Normalizes (schrodingerModel (β := β) hψ)
      ((isometryAction (polarizedForm β)).comp (siegelParabolicGroup β).subtype)
      (siegelParabolicWeil hψ hψ1) :=
  fun p h => standardOperator_comp hψ hψ1 p.1 h

/-- **GKT Corollary 2.18**: `p ↦ (p, r(p))` is a splitting of the Siegel parabolic `P(X)` in the
metaplectic group of pairs of the Schrödinger model. -/
def siegelParabolicSplitting :
    MetaplecticGroup.Splitting (schrodingerModel (β := β) hψ) (siegelParabolicGroup β).subtype :=
  MetaplecticGroup.Splitting.ofNormalizes _ (siegelParabolicWeil_normalizes hψ hψ1)

@[simp] theorem weil_siegelParabolicSplitting :
    (siegelParabolicSplitting hψ hψ1).weil = siegelParabolicWeil (β := β) hψ hψ1 :=
  MetaplecticGroup.Splitting.weil_ofNormalizes _ _

/-- On the Siegel parabolic, the splitting is the standard section `s_r` (GKT p. 60). -/
theorem siegelParabolicSplitting_apply (p : siegelParabolicGroup β) :
    (siegelParabolicSplitting hψ hψ1).toMonoidHom p = standardPair hψ hψ1 p.1 := by
  apply MetaplecticGroup.ext
  · rfl
  · exact LinearEquiv.ext fun φ => rfl

/-- **On the Siegel Levi the standard operator is `siegelLeviWeil`**: for
`m = (a, a')`, `r(m) φ = |det a|^{-1/2} φ(a⁻¹ ·)` (GKT Lemma 2.16 with `b = 0`). -/
theorem standardOperator_siegelLevi (m : siegelLeviGroup β) :
    standardOperator hψ hψ1 (siegelLeviGroup.toIsometry β m) = siegelLeviWeil β m := by
  have hp := siegelLeviGroup.toIsometry_mem m
  have hd : ∀ x, standardD (siegelLeviGroup.toIsometry β m) x = m.1.1.symm x := fun x => by
    change (isometryInv (siegelLeviGroup.toIsometry β m) (x, 0)).1 = _
    rw [isometryInv, ← map_inv, siegelLeviGroup.toIsometry_apply]; rfl
  have hb : ∀ x, standardB (siegelLeviGroup.toIsometry β m) x = 0 := fun x => by
    change (isometryInv (siegelLeviGroup.toIsometry β m) (x, 0)).2 = _
    rw [isometryInv, ← map_inv, siegelLeviGroup.toIsometry_apply]; exact map_zero _
  have hD : siegelD hp = m.1.1.symm := LinearEquiv.ext hd
  have hscal : ((distribHaarChar F (LinearEquiv.det (siegelD hp)) : ℝ) ^ ((1 : ℝ) / 2) : ℝ) =
      ((distribHaarChar F (LinearEquiv.det m.1.1) ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℝ) := by
    have h1 : LinearEquiv.det (siegelD hp) = (LinearEquiv.det m.1.1)⁻¹ := by
      rw [hD]; exact (LinearEquiv.det_symm m.1.1).trans (map_inv LinearEquiv.det m.1.1)
    rw [h1, map_inv (distribHaarChar F), NNReal.coe_inv, NNReal.coe_rpow,
      Real.inv_rpow (NNReal.coe_nonneg _), ← Real.rpow_neg (NNReal.coe_nonneg _), neg_div]
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  rw [standardOperator_of_mem_siegelParabolicGroup hψ hψ1 hp, siegelLeviWeil_apply, hd, hb,
    map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul, hscal]

/-- **GKT Lemma 2.16 for `n(b)`**: `r(n(b)) φ(x) = ψ(-½ β(x, b x)) φ(x)` (the book's
`ψ(½⟨y, -b y⟩) φ(y)`). -/
theorem standardOperator_siegelUnipotentElement (b : X →ₗ[F] Y)
    (hb : ∀ x x', β x (b x') = β x' (b x)) (φ : SchwartzBruhat X) (x : X) :
    (standardOperator hψ hψ1 (siegelUnipotentElement β b hb) φ : X → ℂ) x =
      ψ (-(⅟2 * β x (b x))) * φ x := by
  have hp := siegelUnipotentElement_mem b hb
  have hd : ∀ x, standardD (siegelUnipotentElement β b hb) x = x := fun _ => rfl
  have hbb : ∀ x, standardB (siegelUnipotentElement β b hb) x = -b x := fun x => by
    change (isometryInv (siegelUnipotentElement β b hb) (x, 0)).2 = _
    rw [isometryInv_siegelUnipotentElement]; simp
  have hD : siegelD hp = LinearEquiv.refl F X := LinearEquiv.ext hd
  rw [standardOperator_of_mem_siegelParabolicGroup hψ hψ1 hp, hd, hbb, hD, LinearEquiv.det_refl,
    map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul, map_neg, mul_neg]

end Local

end Langlands.Theta
