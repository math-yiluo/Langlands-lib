import Langlands.Theta.Heisenberg.Schrodinger
import Langlands.LinearAlgebra.Symplectic
import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The Schrödinger representation of the real Heisenberg group

For a finite type `l`, `RealL2 l = L²(ℝˡ)` and `RealSchwartz l = 𝓢(ℝˡ, ℂ)`, on the Euclidean space
`EuclideanSpace ℝ l`. A vector `w ∈ ℝ^{l ⊕ l}` has a translation part `p = translationPart w`
(coordinates `inl`) and a modulation part `q = modulationPart w` (coordinates `inr`).

* The standard symplectic form `ω = stdSymplecticForm l ℝ` on `l ⊕ l → ℝ` is that of
  `Langlands.LinearAlgebra.Symplectic`.
* `schrodingerL2 w`: the unitary operator `f ↦ (x ↦ e^{2πi⟨q, x⟩ + πi⟨p, q⟩} f(x + p))` of
  `L²(ℝˡ)`; the operators satisfy `S(w) S(w') = e^{πi ω(w, w')} S(w + w')` for the standard
  symplectic form `ω` and are the operators `HeisenbergGroup.schrodingerFun` of the pairing `⟪·,·⟫`
  and the character `t ↦ e^{2πit}` (`coeFn_schrodingerL2`). They depend continuously on `w`
  (`continuous_schrodingerL2`).
* `schrodingerSchwartz w`: the same operators on Schwartz space.
* `schrodingerUnitary`: the unitary representation of the real Heisenberg group
  `HeisenbergGroup (stdSymplecticForm l ℝ)`, `(w, t) ↦ e^{2πit} S(w)`.
-/

noncomputable section

open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff InnerProductSpace

namespace Langlands.Theta

namespace Real

universe u

/-- `L²(ℝˡ)`, on the Euclidean space with index set `l`. -/
abbrev RealL2 (l : Type) [Fintype l] : Type := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ l))

/-- The Schwartz space `𝓢(ℝˡ, ℂ)`. -/
abbrev RealSchwartz (l : Type) [Fintype l] : Type := 𝓢(EuclideanSpace ℝ l, ℂ)

/-- The inclusion of Schwartz space in `L²(ℝˡ)`: Mathlib's `SchwartzMap.toLpCLM`. -/
scoped notation:max "schwartzToL2 " l:max =>
  (SchwartzMap.toLpCLM ℂ ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ l)) :
    RealSchwartz l →L[ℂ] RealL2 l)

section Coordinates

variable {l : Type}

/-- The translation part `(w (inl i))ᵢ` of `w ∈ ℝ^{l ⊕ l}`. -/
def translationPart (w : l ⊕ l → ℝ) : EuclideanSpace ℝ l := WithLp.toLp 2 fun i => w (Sum.inl i)

/-- The modulation part `(w (inr i))ᵢ` of `w ∈ ℝ^{l ⊕ l}`. -/
def modulationPart (w : l ⊕ l → ℝ) : EuclideanSpace ℝ l := WithLp.toLp 2 fun i => w (Sum.inr i)

/-- The translation part is additive. -/
theorem translationPart_add (w w' : l ⊕ l → ℝ) :
    translationPart (w + w') = translationPart w + translationPart w' := rfl

/-- The modulation part is additive. -/
theorem modulationPart_add (w w' : l ⊕ l → ℝ) :
    modulationPart (w + w') = modulationPart w + modulationPart w' := rfl

/-- The translation part is linear. -/
theorem translationPart_smul (t : ℝ) (w : l ⊕ l → ℝ) :
    translationPart (t • w) = t • translationPart w := rfl

/-- The modulation part is linear. -/
theorem modulationPart_smul (t : ℝ) (w : l ⊕ l → ℝ) :
    modulationPart (t • w) = t • modulationPart w := rfl

/-- The translation part of `-w`. -/
theorem translationPart_neg (w : l ⊕ l → ℝ) : translationPart (-w) = -translationPart w := rfl

/-- The modulation part of `-w`. -/
theorem modulationPart_neg (w : l ⊕ l → ℝ) : modulationPart (-w) = -modulationPart w := rfl

/-- The translation part of `0`. -/
@[simp] theorem translationPart_zero : translationPart (0 : l ⊕ l → ℝ) = 0 := rfl

/-- The modulation part of `0`. -/
@[simp] theorem modulationPart_zero : modulationPart (0 : l ⊕ l → ℝ) = 0 := rfl

/-- The coordinates of the translation part. -/
@[simp] theorem translationPart_apply (w : l ⊕ l → ℝ) (i : l) : translationPart w i = w (Sum.inl i) :=
  rfl

/-- The coordinates of the modulation part. -/
@[simp] theorem modulationPart_apply (w : l ⊕ l → ℝ) (i : l) : modulationPart w i = w (Sum.inr i) :=
  rfl

/-- The translation part is continuous. -/
theorem continuous_translationPart : Continuous (translationPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold translationPart
  fun_prop

/-- The modulation part is continuous. -/
theorem continuous_modulationPart : Continuous (modulationPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold modulationPart
  fun_prop

end Coordinates


section Character

/-- The character `t ↦ e^{2πit}` of `ℝ` with complex values: Mathlib's `Real.fourierChar`
composed with the inclusion of the circle. -/
def fourierCharℂ : AddChar ℝ ℂ := Circle.coeHom.compAddChar Real.fourierChar

/-- `fourierCharℂ x = e^{2πix}`. -/
theorem fourierCharℂ_apply (x : ℝ) : fourierCharℂ x = cexp (2 * π * x * I) := by
  show ((Real.fourierChar x : Circle) : ℂ) = _
  rw [Real.fourierChar_apply]
  push_cast
  ring_nf

/-- The character has modulus one. -/
theorem norm_fourierCharℂ (x : ℝ) : ‖fourierCharℂ x‖ = 1 := Circle.norm_coe _

/-- The character is continuous. -/
theorem continuous_fourierCharℂ : Continuous fourierCharℂ := by
  have : (fourierCharℂ : ℝ → ℂ) = fun x : ℝ => cexp (2 * π * (x : ℂ) * I) :=
    funext fourierCharℂ_apply
  rw [this]
  fun_prop

/-- The character has temperate growth (it multiplies Schwartz space). -/
theorem hasTemperateGrowth_fourierCharℂ : Function.HasTemperateGrowth (fourierCharℂ : ℝ → ℂ) := by
  have hf : (fourierCharℂ : ℝ → ℂ) = fun x : ℝ => cexp (2 * π * x * I) := funext fourierCharℂ_apply
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (2 * π * y * I : ℂ)) (2 * π * I) x := by
    intro x
    have h := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * π : ℂ)).mul_const I
    simpa using h
  have hd : ∀ c : ℂ, deriv (fun x : ℝ => c * cexp (2 * π * x * I)) =
      fun x : ℝ => c * (2 * π * I) * cexp (2 * π * x * I) := by
    intro c
    funext x
    rw [((hlin x).cexp.const_mul c).deriv]
    ring
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => cexp (2 * π * x * I)) =
      fun x : ℝ => (2 * π * I) ^ n * cexp (2 * π * x * I) := by
    intro n
    induction n with
    | zero => funext x; simp
    | succ n ih => rw [iteratedDeriv_succ, ih, hd, pow_succ]
  have hnorm : ∀ x : ℝ, ‖cexp (2 * π * x * I)‖ = 1 := by
    intro x
    rw [show (2 * π * x * I : ℂ) = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hf]
  refine ⟨?_, fun n => ⟨0, (2 * π) ^ n, fun x => ?_⟩⟩
  · exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit n]
    simp only [norm_mul, norm_pow, hnorm, mul_one, pow_zero]
    simp [abs_of_pos Real.pi_pos]

end Character

variable {l : Type} [Fintype l]

namespace Internal

/-- The symplectic pairing in the coordinates of the proofs: `⟪p, q'⟫ - ⟪q, p'⟫`. -/
def sympl (w w' : l ⊕ l → ℝ) : ℝ :=
  ⟪translationPart w, modulationPart w'⟫ - ⟪modulationPart w, translationPart w'⟫

theorem sympl_eq_stdSymplecticForm (w w' : l ⊕ l → ℝ) : sympl w w' = stdSymplecticForm l ℝ w w' := by
  simp only [sympl, stdSymplecticForm_apply_eq_sum, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, translationPart_apply, modulationPart_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The phase `e^{2πi⟨q, x⟩ + πi⟨p, q⟩}` of the Schrödinger operator of `w = (p, q)`. -/
def schrodingerPhase (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) : ℂ :=
  exp (((2 * π * ⟪modulationPart w, x⟫ + π * ⟪translationPart w, modulationPart w⟫ : ℝ) : ℂ) * I)

/-- The Schrödinger operator on functions, in the form of the proofs. -/
def rhoFun (w : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) : EuclideanSpace ℝ l → ℂ :=
  fun x => schrodingerPhase w x * f (x + translationPart w)

theorem norm_schrodingerPhase (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) : ‖schrodingerPhase w x‖ = 1 :=
  norm_exp_ofReal_mul_I _

theorem continuous_schrodingerPhase (w : l ⊕ l → ℝ) : Continuous (schrodingerPhase w) := by
  unfold schrodingerPhase
  fun_prop

theorem schrodingerPhase_eq_fourierCharℂ (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    schrodingerPhase w x =
      fourierCharℂ (⟪modulationPart w, x⟫ + ⟪translationPart w, modulationPart w⟫ / 2) := by
  rw [fourierCharℂ_apply, schrodingerPhase]
  congr 1
  push_cast
  ring

theorem hasTemperateGrowth_schrodingerPhase (w : l ⊕ l → ℝ) :
    Function.HasTemperateGrowth (schrodingerPhase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪modulationPart w, x⟫ :=
    (innerSL ℝ (modulationPart w)).hasTemperateGrowth
  have h := hasTemperateGrowth_fourierCharℂ.comp
    (h1.add (Function.HasTemperateGrowth.const (⟪translationPart w, modulationPart w⟫ / 2)))
  have e : schrodingerPhase w = (fourierCharℂ : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪modulationPart w, x⟫) +
        fun _ => ⟪translationPart w, modulationPart w⟫ / 2) := by
    funext x
    simp [schrodingerPhase_eq_fourierCharℂ]
  rw [e]
  exact h

theorem rhoFun_rhoFun (w w' : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) :
    rhoFun w (rhoFun w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rhoFun (w + w') f := by
  funext x
  simp only [rhoFun, schrodingerPhase, Pi.smul_apply, smul_eq_mul, translationPart_add,
    modulationPart_add, ← mul_assoc, ← Complex.exp_add, add_assoc x]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [sympl, inner_add_left, inner_add_right, real_inner_comm (translationPart w) (modulationPart w'),
    real_inner_comm (modulationPart w) (translationPart w')]
  ring

theorem rhoFun_zero (f : EuclideanSpace ℝ l → ℂ) : rhoFun 0 f = f := by
  funext x
  simp [rhoFun, schrodingerPhase]

theorem rhoFun_congr (w : l ⊕ l → ℝ) {f g : EuclideanSpace ℝ l → ℂ} (h : f =ᵐ[volume] g) :
    rhoFun w f =ᵐ[volume] rhoFun w g := by
  filter_upwards [(measurePreserving_add_right volume (translationPart w)).quasiMeasurePreserving.ae_eq_comp h]
    with x hx
  simp only [rhoFun]
  rw [show f (x + translationPart w) = g (x + translationPart w) from hx]

theorem eLpNorm_rhoFun (w : l ⊕ l → ℝ) (f : RealL2 l) :
    eLpNorm (rhoFun w f) 2 volume = eLpNorm f 2 volume := by
  have hm := (Lp.aestronglyMeasurable f).comp_measurePreserving
    (measurePreserving_add_right volume (translationPart w))
  rw [← eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f)
    (measurePreserving_add_right volume (translationPart w))]
  refine eLpNorm_congr_norm_ae ((continuous_schrodingerPhase w).aestronglyMeasurable.mul hm) hm
    (.of_forall fun x => ?_)
  simp [rhoFun, norm_schrodingerPhase]

theorem memLp_rhoFun (w : l ⊕ l → ℝ) (f : RealL2 l) : MemLp (rhoFun w f) 2 volume := by
  rw [memLp_iff, eLpNorm_rhoFun]; exact Lp.eLpNorm_lt_top f

/-- The Schrödinger operator of `w` as a linear isometry of `L²`. -/
def rhoIsometry (w : l ⊕ l → ℝ) : RealL2 l →ₗᵢ[ℂ] RealL2 l where
  toFun f := (memLp_rhoFun w f).toLp
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ((rhoFun_congr w (Lp.coeFn_add f g)).trans (.of_forall fun x => ?_))
    simp [rhoFun, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ((rhoFun_congr w (Lp.coeFn_smul c f)).trans (.of_forall fun x => ?_))
    simp [rhoFun, mul_left_comm]
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, eLpNorm_rhoFun, Lp.norm_def]

theorem coeFn_rhoIsometry (w : l ⊕ l → ℝ) (f : RealL2 l) : rhoIsometry w f =ᵐ[volume] rhoFun w f :=
  (memLp_rhoFun w f).coeFn_toLp

theorem rhoIsometry_rhoIsometry (w w' : l ⊕ l → ℝ) (f : RealL2 l) :
    rhoIsometry w (rhoIsometry w' f) =
      exp (((π * sympl w w' : ℝ) : ℂ) * I) • rhoIsometry (w + w') f := by
  refine Lp.ext ((coeFn_rhoIsometry _ _).trans ((rhoFun_congr w (coeFn_rhoIsometry _ _)).trans ?_))
  rw [rhoFun_rhoFun]
  filter_upwards [Lp.coeFn_smul (exp (((π * sympl w w' : ℝ) : ℂ) * I)) (rhoIsometry (w + w') f),
    coeFn_rhoIsometry (w + w') f] with x h1 h2
  rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

theorem rhoIsometry_zero (f : RealL2 l) : rhoIsometry 0 f = f :=
  Lp.ext ((coeFn_rhoIsometry _ _).trans (by rw [rhoFun_zero]))

end Internal

open Internal

/-- The Schrödinger operator of `w = (p, q)` on `L²(ℝˡ)`:
`f ↦ (x ↦ e^{2πi⟨q, x⟩ + πi⟨p, q⟩} f(x + p))`. -/
def schrodingerL2 (w : l ⊕ l → ℝ) : RealL2 l ≃ₗᵢ[ℂ] RealL2 l :=
  LinearIsometryEquiv.ofSurjective (rhoIsometry w) fun f =>
    ⟨(exp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rhoIsometry (-w) f, by
      rw [map_smul, rhoIsometry_rhoIsometry, add_neg_cancel, rhoIsometry_zero,
        inv_smul_smul₀ (exp_ne_zero _)]⟩

namespace Internal

theorem coeFn_schrodingerL2_eq_rhoFun (w : l ⊕ l → ℝ) (f : RealL2 l) :
    schrodingerL2 w f =ᵐ[volume] rhoFun w f :=
  coeFn_rhoIsometry w f

theorem schrodingerL2_schrodingerL2 (w w' : l ⊕ l → ℝ) (f : RealL2 l) :
    schrodingerL2 w (schrodingerL2 w' f) =
      exp (((π * sympl w w' : ℝ) : ℂ) * I) • schrodingerL2 (w + w') f :=
  rhoIsometry_rhoIsometry w w' f

/-- The operators of the proofs are the general Schrödinger operators. -/
theorem rhoFun_eq_schrodingerFun (w : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) :
    rhoFun w f = HeisenbergGroup.schrodingerFun fourierCharℂ (innerₗ (EuclideanSpace ℝ l))
      (translationPart w, modulationPart w) f := by
  funext x
  rw [rhoFun, schrodingerPhase_eq_fourierCharℂ, HeisenbergGroup.schrodingerFun_apply]
  congr 2
  simp only [innerₗ_apply_apply, real_inner_comm x, invOf_eq_inv]
  ring

end Internal

/-- The Schrödinger operators on functions on `ℝˡ`, explicitly:
`(x ↦ e^{2πi⟨x, q⟩ + πi⟨p, q⟩} f(x + p))`. -/
theorem schrodingerFun_real (w : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    HeisenbergGroup.schrodingerFun fourierCharℂ (innerₗ (EuclideanSpace ℝ l))
      (translationPart w, modulationPart w) f x =
      cexp ((2 * π * ⟪x, modulationPart w⟫ + π * ⟪translationPart w, modulationPart w⟫ : ℝ) * I) *
        f (x + translationPart w) := by
  rw [← rhoFun_eq_schrodingerFun, rhoFun, schrodingerPhase, real_inner_comm (modulationPart w) x]

/-- Almost everywhere, `schrodingerL2 w f` is the Schrödinger operator
`HeisenbergGroup.schrodingerFun` of the pairing `⟪·,·⟫`, the character `t ↦ e^{2πit}` and `w =
(translationPart w, modulationPart w)` applied to `f`. -/
theorem coeFn_schrodingerL2 (w : l ⊕ l → ℝ) (f : RealL2 l) :
    schrodingerL2 w f =ᵐ[volume] HeisenbergGroup.schrodingerFun fourierCharℂ
      (innerₗ (EuclideanSpace ℝ l)) (translationPart w, modulationPart w) f := by
  rw [← rhoFun_eq_schrodingerFun]
  exact coeFn_schrodingerL2_eq_rhoFun w f

/-- The Schrödinger operators form a projective representation: `S(w) S(w') = e^{πi ω(w, w')} S(w +
w')`. -/
theorem schrodingerL2_comp (w w' : l ⊕ l → ℝ) (f : RealL2 l) :
    schrodingerL2 w (schrodingerL2 w' f) =
      Complex.exp (π * stdSymplecticForm l ℝ w w' * I) • schrodingerL2 (w + w') f := by
  rw [schrodingerL2_schrodingerL2, sympl_eq_stdSymplecticForm]
  push_cast
  rfl

/-- `schrodingerL2 0` is the identity. -/
theorem schrodingerL2_zero (f : RealL2 l) : schrodingerL2 0 f = f := rhoIsometry_zero f

/-- The Schrödinger operators of Schwartz functions. -/
def schrodingerSchwartz (w : l ⊕ l → ℝ) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  SchwartzMap.smulLeftCLM ℂ (schrodingerPhase w) ∘L SchwartzMap.compSubConstCLM ℂ (-translationPart w)

namespace Internal

theorem coe_schrodingerSchwartz_eq_rhoFun (w : l ⊕ l → ℝ) (f : RealSchwartz l) :
    ⇑(schrodingerSchwartz w f) = rhoFun w ⇑f := by
  funext x
  rw [schrodingerSchwartz, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_schrodingerPhase w),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, rhoFun]

end Internal

/-- On Schwartz space the operator is the Schrödinger operator `HeisenbergGroup.schrodingerFun`. -/
theorem coe_schrodingerSchwartz (w : l ⊕ l → ℝ) (f : RealSchwartz l) :
    ⇑(schrodingerSchwartz w f) = HeisenbergGroup.schrodingerFun fourierCharℂ
      (innerₗ (EuclideanSpace ℝ l)) (translationPart w, modulationPart w) f := by
  rw [coe_schrodingerSchwartz_eq_rhoFun, rhoFun_eq_schrodingerFun]

/-- On Schwartz functions, the operators of `L²` are those of Schwartz space. -/
theorem schrodingerL2_toLp (w : l ⊕ l → ℝ) (f : RealSchwartz l) :
    schrodingerL2 w (f.toLp 2) = (schrodingerSchwartz w f).toLp 2 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_schrodingerL2_eq_rhoFun w (f.toLp 2), rhoFun_congr w (f.coeFn_toLp 2 volume),
    (schrodingerSchwartz w f).coeFn_toLp 2 volume] with x h1 h2 h3
  rw [h1, h2, h3, coe_schrodingerSchwartz_eq_rhoFun]

namespace Internal

theorem continuous_inner_schrodingerL2_toLp (φ f : RealSchwartz l) :
    Continuous fun w : l ⊕ l → ℝ => ⟪φ.toLp 2, schrodingerL2 w (f.toLp 2)⟫_ℂ := by
  have e : ∀ w : l ⊕ l → ℝ, ⟪φ.toLp 2, schrodingerL2 w (f.toLp 2)⟫_ℂ =
      ∫ x, starRingEnd ℂ (φ x) * rhoFun w f x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_schrodingerL2_eq_rhoFun w (f.toLp 2),
      rhoFun_congr w (f.coeFn_toLp 2 volume)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp [mul_comm]
  simp only [e]
  refine continuous_of_dominated (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 f) (fun w => ?_)
    (fun w => .of_forall fun x => ?_) ((φ.integrable (μ := volume)).norm.mul_const _)
    (.of_forall fun x => ?_)
  · exact ((continuous_star.comp φ.continuous).mul
      ((continuous_schrodingerPhase w).mul (f.continuous.comp (continuous_add_const _)))).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj, rhoFun, norm_mul, norm_schrodingerPhase, one_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  · simp only [rhoFun, schrodingerPhase]
    have := continuous_translationPart (l := l)
    have := continuous_modulationPart (l := l)
    fun_prop

theorem continuous_schrodingerL2_toLp (f : RealSchwartz l) :
    Continuous fun w : l ⊕ l → ℝ => schrodingerL2 w (f.toLp 2) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  set v : RealL2 l := f.toLp 2 with hv
  set g : RealL2 l := (schrodingerSchwartz w₀ f).toLp 2 with hg
  have h0 : schrodingerL2 w₀ v = g := schrodingerL2_toLp w₀ f
  have hsq : ∀ w, ‖schrodingerL2 w v - schrodingerL2 w₀ v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * (⟪g, schrodingerL2 w v⟫_ℂ).re := by
    intro w
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm, h0,
      RCLike.re_to_complex]
    ring
  have hc : Continuous fun w => ‖schrodingerL2 w v - schrodingerL2 w₀ v‖ ^ 2 := by
    simp only [hsq]
    exact continuous_const.sub (continuous_const.mul
      (continuous_re.comp (continuous_inner_schrodingerL2_toLp (schrodingerSchwartz w₀ f) f)))
  have ht := hc.tendsto w₀
  simp only [sub_self, norm_zero] at ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp ht
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

theorem continuous_schrodingerL2_prod :
    Continuous fun x : RealL2 l × (l ⊕ l → ℝ) => schrodingerL2 x.2 x.1 := by
  have hd : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact continuous_prod_of_dense_continuous_lipschitzWith
    (fun x : RealL2 l × (l ⊕ l → ℝ) => schrodingerL2 x.2 x.1) 1 hd
    (by rintro _ ⟨f, rfl⟩; exact continuous_schrodingerL2_toLp f)
    fun w => (schrodingerL2 w).lipschitzWith

end Internal

/-- The Schrödinger operators depend jointly continuously on `w` and the vector. -/
theorem continuous_schrodingerL2_uncurry :
    Continuous fun x : (l ⊕ l → ℝ) × RealL2 l => schrodingerL2 x.1 x.2 :=
  (continuous_schrodingerL2_prod (l := l)).comp
    (f := fun x : (l ⊕ l → ℝ) × RealL2 l => ((x.2, x.1) : RealL2 l × (l ⊕ l → ℝ)))
    (continuous_snd.prodMk continuous_fst)

/-- Strong continuity: `w ↦ schrodingerL2 w f` is continuous. -/
theorem continuous_schrodingerL2 (f : RealL2 l) : Continuous fun w => schrodingerL2 w f :=
  (continuous_schrodingerL2_prod (l := l)).comp
    (f := fun w : l ⊕ l → ℝ => ((f, w) : RealL2 l × (l ⊕ l → ℝ)))
    (Continuous.prodMk continuous_const continuous_id)

section Unitary

/-- Multiplication by a complex number of modulus one, as a linear isometry. -/
def circleSMul (z : Circle) : RealL2 l ≃ₗᵢ[ℂ] RealL2 l :=
  { LinearEquiv.smulOfUnit (Circle.toUnits z) with
    norm_map' := fun v => by
      show ‖(z : ℂ) • v‖ = ‖v‖
      rw [norm_smul, Circle.norm_coe, one_mul] }

/-- The value of `circleSMul`. -/
@[simp] theorem circleSMul_apply (z : Circle) (v : RealL2 l) : circleSMul z v = (z : ℂ) • v := rfl

/-- The unitary representation of the real Heisenberg group: `(w, t)` acts by
`e^{2πit} schrodingerL2 w`. -/
def schrodingerUnitary : HeisenbergGroup (stdSymplecticForm l ℝ) →* (RealL2 l ≃ₗᵢ[ℂ] RealL2 l) where
  toFun g := (schrodingerL2 g.vec).trans (circleSMul (Real.fourierChar g.cen))
  map_one' := by
    ext f
    simp [schrodingerL2_zero]
  map_mul' g h := by
    ext1 f
    simp only [LinearIsometryEquiv.trans_apply, circleSMul_apply, HeisenbergGroup.mul_vec,
      HeisenbergGroup.mul_cen, LinearIsometryEquiv.coe_mul, Function.comp_apply, map_smul]
    rw [schrodingerL2_comp, smul_smul, smul_smul]
    congr 1
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    simp only [Circle.coe_mul, Real.fourierChar_apply, invOf_eq_inv]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- `(w, t)` acts by `e^{2πit} schrodingerL2 w`. -/
theorem schrodingerUnitary_apply (g : HeisenbergGroup (stdSymplecticForm l ℝ)) (f : RealL2 l) :
    schrodingerUnitary g f = fourierCharℂ g.cen • schrodingerL2 g.vec f := rfl

end Unitary

end Real

end Langlands.Theta
