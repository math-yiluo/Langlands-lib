import Langlands.Theta.Real.Intertwiner
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# The operators of the big cell

The operators of Schwartz space from which the metaplectic group is built over the big cell
`{det A ≠ 0}` of `Sp_{2l}(ℝ)`:

* `chirp S`: multiplication by `e^{-πi⟨x, S x⟩}`;
* `dilation B`: `f ↦ f ∘ B`;
* Mathlib's Fourier transform `fourierCLM ℂ (RealSchwartz l)` and its inverse;
* `bigCellOp Ai B C c = chirp (C Ai) ∘ (c • dilation Ai) ∘ 𝓕 ∘ chirp (-(Ai B)) ∘ 𝓕⁻¹`.

Each of them preserves the `L²` norm (for `c² = |det Ai|` in the last case) and carries the
Schrödinger operator of `(p, q)` to that of an explicitly given `(p', q')`: the chirp to
`(p, q + S p)`, the dilation to `(B⁻¹ p, Bᵀ q)`, the Fourier transform to `(-q, p)`; for
`g = [[A, B], [C, D]]` symplectic with `A` invertible, `bigCellOp A⁻¹ B C |det A|^{-1/2}` carries
`(p, q)` to `g (p, q)` (`Internal.intertwinesAt_bigCellOp`). This is the classical formula
for the metaplectic operators on the big cell (G. B. Folland, *Harmonic analysis in phase space*
(1989), chapter 4, §4, Theorem (4.51), p. 191, proved on p. 192 from the factorization of
Proposition (4.9) and the operators (4.24)–(4.26) of §2, p. 179).
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform
open scoped Real RealInnerProductSpace FourierTransform

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l]

namespace Real

/-- A shortcut: the default instance search for it exceeds the default limit
(`synthInstance.maxHeartbeats`) on this Mathlib. -/
instance instHasSummableGeomSeriesEuclidean (l : Type) [Fintype l] :
    HasSummableGeomSeries (EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) :=
  @instHasSummableGeomSeriesOfCompleteSpace _ _ ContinuousLinearMap.instCompleteSpace

namespace Internal

def rf (p q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) : EuclideanSpace ℝ l → ℂ :=
  fun x => exp (((2 * π * ⟪q, x⟫ + π * ⟪p, q⟫ : ℝ) : ℂ) * I) * f (x + p)

theorem rhoFun_eq (w : l ⊕ l → ℝ) (f : EuclideanSpace ℝ l → ℂ) : rhoFun w f = rf (translationPart w) (modulationPart w) f := rfl

def IntertwinesAt (S : RealSchwartz l →L[ℂ] RealSchwartz l) (p q p' q' : EuclideanSpace ℝ l) : Prop :=
  ∀ f g : RealSchwartz l, ⇑g = rf p q f → ⇑(S g) = rf p' q' (S f)

def IsL2Isometry (S : RealSchwartz l →L[ℂ] RealSchwartz l) : Prop := ∀ f, ‖schwartzToL2 l (S f)‖ = ‖schwartzToL2 l f‖

theorem IntertwinesAt.mul {S T : RealSchwartz l →L[ℂ] RealSchwartz l} {p q p' q' p'' q'' : EuclideanSpace ℝ l} (hS : IntertwinesAt S p' q' p'' q'') (hT : IntertwinesAt T p q p' q') :
    IntertwinesAt (S * T) p q p'' q'' := fun f g h => hS _ _ (hT f g h)

theorem IntertwinesAt.smul {S : RealSchwartz l →L[ℂ] RealSchwartz l} {p q p' q' : EuclideanSpace ℝ l} (hS : IntertwinesAt S p q p' q') (c : ℂ) :
    IntertwinesAt (c • S) p q p' q' := fun f g h => by
  funext x
  have := congrFun (hS f g h) x
  simp only [rf, _root_.smul_apply, _root_.smul_apply, smul_eq_mul] at this ⊢
  rw [this]
  ring

theorem IsL2Isometry.mul {S T : RealSchwartz l →L[ℂ] RealSchwartz l} (hS : IsL2Isometry S) (hT : IsL2Isometry T) : IsL2Isometry (S * T) := fun f => (hS _).trans (hT f)

theorem isL2Isometry_of_integral {S : RealSchwartz l →L[ℂ] RealSchwartz l} (h : ∀ f : RealSchwartz l, ∫ x, ‖S f x‖ ^ (2 : ℝ) = ∫ x, ‖f x‖ ^ (2 : ℝ)) : IsL2Isometry S :=
  fun f => by
    rw [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, norm_toLp' (by simp) (by simp), norm_toLp' (by simp) (by simp)]
    simp only [ENNReal.toReal_ofNat, h]

theorem temperate_quad (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪x, S x⟫ :=
  (innerSL ℝ).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' S.hasTemperateGrowth

end Internal

/-- The chirp `f ↦ e^{-πi⟨x, S x⟩} f` (multiplication by a Gaussian character of second
degree). -/
def chirp (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  smulLeftCLM ℂ fun x : EuclideanSpace ℝ l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I)

/-- `chirp S f x = e^{-πi⟨x, S x⟩} f(x)`. -/
theorem chirp_apply (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) :
    chirp S f x = exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) * f x := by
  have h2 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => (-2⁻¹ : ℝ) * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) := by
    convert hasTemperateGrowth_fourierCharℂ.comp h2 using 1
    funext x
    simp only [Function.comp, fourierCharℂ_apply]
    congr 1
    push_cast
    ring
  rw [chirp, smulLeftCLM_apply_apply h3, smul_eq_mul]

/-- `chirp S ∘ chirp T = chirp (S + T)`. -/
theorem chirp_mul (S T : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : chirp S * chirp T = chirp (S + T) := by
  ext f x
  simp only [mul_apply_eq_comp, chirp_apply, ← mul_assoc, ← Complex.exp_add, _root_.add_apply,
    inner_add_right]
  congr 2
  push_cast
  ring

/-- `chirp 0 = 1`. -/
theorem chirp_zero : chirp (0 : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) = 1 := by
  ext f x
  simp [chirp_apply]

/-- The chirps are invertible. -/
theorem isUnit_chirp (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : IsUnit (chirp S) :=
  ⟨⟨chirp S, chirp (-S), by rw [chirp_mul, add_neg_cancel, chirp_zero], by rw [chirp_mul, neg_add_cancel, chirp_zero]⟩, rfl⟩

namespace Internal

theorem isL2Isometry_chirp (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : IsL2Isometry (chirp S) := isL2Isometry_of_integral fun f => by
  simp only [chirp_apply, norm_mul, norm_exp_ofReal_mul_I, one_mul]

theorem intertwinesAt_chirp {S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (hS : ∀ x y, ⟪x, S y⟫ = ⟪y, S x⟫) (p q : EuclideanSpace ℝ l) : IntertwinesAt (chirp S) p q p (q + S p) :=
  fun f g h => by
    funext x
    simp only [rf, chirp_apply, h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
    congr 2
    simp only [inner_add_left, inner_add_right, map_add, hS p x, real_inner_comm x (S p)]
    ring

end Internal

open Classical in
/-- The dilation `f ↦ f ∘ B` (for invertible `B`; `0` otherwise). -/
def dilation (B : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  if h : IsUnit B then compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.ofUnit h.unit) else 0

/-- `dilation B f x = f (B x)` for invertible `B`. -/
theorem dilation_apply {B : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (h : IsUnit B) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) : dilation B f x = f (B x) := by
  rw [dilation, dite_eq_left h]
  rfl

/-- `dilation 1 = 1`. -/
theorem dilation_one : dilation (1 : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) = 1 := by
  ext f x
  simp [dilation_apply isUnit_one]

/-- `dilation A ∘ dilation B = dilation (B A)`. -/
theorem dilation_mul {A B : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (hA : IsUnit A) (hB : IsUnit B) : dilation A * dilation B = dilation (B * A) := by
  ext f x
  simp [dilation_apply, hA, hB, hB.mul hA]

/-- The dilations of invertible maps are invertible. -/
theorem isUnit_dilation {B : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (h : IsUnit B) : IsUnit (dilation B) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨dilation u, dilation (u⁻¹ : (EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l)ˣ), by rw [dilation_mul u.isUnit u⁻¹.isUnit, Units.inv_mul, dilation_one],
    by rw [dilation_mul u⁻¹.isUnit u.isUnit, Units.mul_inv, dilation_one]⟩, rfl⟩

namespace Internal

theorem intertwinesAt_dilation {B : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (hB : IsUnit B) {p q p' q' : EuclideanSpace ℝ l} (hp : B p' = p) (hq : ∀ x, ⟪q', x⟫ = ⟪q, B x⟫) :
    IntertwinesAt (dilation B) p q p' q' := fun f g h => by
  funext x
  simp only [rf, dilation_apply hB, h, map_add, hp, real_inner_comm q' p', hq, real_inner_comm q p]

theorem isL2Isometry_dilation {B : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (hB : IsUnit B) {c : ℝ} (hc : c ^ 2 = |B.det|) : IsL2Isometry ((c : ℂ) • dilation B) :=
  isL2Isometry_of_integral fun f => by
    have hd : LinearMap.det (B : EuclideanSpace ℝ l →ₗ[ℝ] EuclideanSpace ℝ l) ≠ 0 :=
      ((hB.map ContinuousLinearMap.toLinearMapRingHom).map LinearMap.det).ne_zero
    have h1 := integral_map (μ := volume) (φ := (B : EuclideanSpace ℝ l →ₗ[ℝ] EuclideanSpace ℝ l)) (f := fun x => ‖f x‖ ^ (2 : ℝ))
      B.continuous.aemeasurable (f.continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hd, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    simp only [_root_.smul_apply, _root_.smul_apply, dilation_apply hB, norm_smul, norm_real, Real.rpow_two,
      mul_pow, Real.norm_eq_abs, sq_abs, hc, integral_const_mul] at h1 ⊢
    erw [← h1]
    rw [smul_eq_mul, ← mul_assoc, ← abs_mul, ContinuousLinearMap.det, mul_inv_cancel₀ hd, abs_one, one_mul]

theorem fourierCLM_mul_fourierInvCLM : fourierCLM ℂ (RealSchwartz l) * fourierInvCLM ℂ (RealSchwartz l) = 1 := by
  ext1 f
  rw [mul_apply_eq_comp, FourierTransform.fourierCLM_apply, FourierTransform.fourierInvCLM_apply, FourierTransform.fourier_fourierInv_eq]
  rfl

theorem fourierInvCLM_mul_fourierCLM : fourierInvCLM ℂ (RealSchwartz l) * fourierCLM ℂ (RealSchwartz l) = 1 := by
  ext1 f
  rw [mul_apply_eq_comp, FourierTransform.fourierCLM_apply, FourierTransform.fourierInvCLM_apply, FourierTransform.fourierInv_fourier_eq]
  rfl

theorem isUnit_fourierCLM : IsUnit (fourierCLM ℂ (RealSchwartz l)) := ⟨⟨_, _, fourierCLM_mul_fourierInvCLM, fourierInvCLM_mul_fourierCLM⟩, rfl⟩

theorem isUnit_fourierInvCLM : IsUnit (fourierInvCLM ℂ (RealSchwartz l)) := ⟨⟨_, _, fourierInvCLM_mul_fourierCLM, fourierCLM_mul_fourierInvCLM⟩, rfl⟩

theorem isL2Isometry_fourierCLM : IsL2Isometry (fourierCLM ℂ (RealSchwartz l)) := fun f => norm_fourier_toL2_eq f

theorem isL2Isometry_fourierInvCLM : IsL2Isometry (fourierInvCLM ℂ (RealSchwartz l)) := fun f => by
  rw [← isL2Isometry_fourierCLM (fourierInvCLM ℂ (RealSchwartz l) f), ← mul_apply_eq_comp, fourierCLM_mul_fourierInvCLM, one_apply_eq_self]

theorem intertwinesAt_fourierCLM (p q : EuclideanSpace ℝ l) : IntertwinesAt (fourierCLM ℂ (RealSchwartz l)) p q (-q) p := fun f g h => by
  funext x
  simp only [FourierTransform.fourierCLM_apply, fourier_coe, rf, h, Real.fourier_eq', smul_eq_mul]
  rw [← integral_const_mul, ← integral_add_right_eq_self (μ := volume) (fun v => exp (((2 * π * ⟪p, x⟫ + π * ⟪-q, p⟫ : ℝ) : ℂ) * I) *
    (exp (((-2 * π * ⟪v, x + -q⟫ : ℝ) : ℂ) * I) * f v)) p]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_comm q p, real_inner_comm q v]
  ring

theorem intertwinesAt_fourierInvCLM (p q : EuclideanSpace ℝ l) : IntertwinesAt (fourierInvCLM ℂ (RealSchwartz l)) p q q (-p) := fun f g h => by
  funext x
  have h1 := congrFun (intertwinesAt_fourierCLM p q f g h) (-x)
  have e : ∀ (u : RealSchwartz l) y, fourierInvCLM ℂ (RealSchwartz l) u y = fourierCLM ℂ (RealSchwartz l) u (-y) := fun u y => rfl
  rw [e, h1]
  simp only [rf, e, inner_neg_left, inner_neg_right, neg_add]

end Internal

/-- The explicit operator of an element of the big cell of `Sp`:
`chirp (C A⁻¹) ∘ c · dilation A⁻¹ ∘ 𝓕 ∘ chirp (-A⁻¹ B) ∘ 𝓕⁻¹`, with `c = |det A|^{-1/2}`
in the applications. -/
def bigCellOp (Ai B C : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (c : ℝ) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  chirp (C * Ai) * (((c : ℂ) • dilation Ai) * (fourierCLM ℂ (RealSchwartz l) * (chirp (-(Ai * B)) * fourierInvCLM ℂ (RealSchwartz l))))

/-- The big-cell operators are invertible. -/
theorem isUnit_bigCellOp {Ai : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (h : IsUnit Ai) (B C : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) {c : ℝ} (hc : c ≠ 0) :
    IsUnit (bigCellOp Ai B C c) := by
  refine (isUnit_chirp _).mul (IsUnit.mul ?_ (isUnit_fourierCLM.mul ((isUnit_chirp _).mul isUnit_fourierInvCLM)))
  rw [Algebra.smul_def]
  exact ((IsUnit.mk0 (c : ℂ) (by simpa using hc)).map _).mul (isUnit_dilation h)

namespace Internal

theorem isL2Isometry_bigCellOp {Ai : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (h : IsUnit Ai) (B C : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) {c : ℝ} (hc : c ^ 2 = |Ai.det|) :
    IsL2Isometry (bigCellOp Ai B C c) :=
  (isL2Isometry_chirp _).mul ((isL2Isometry_dilation h hc).mul (isL2Isometry_fourierCLM.mul ((isL2Isometry_chirp _).mul isL2Isometry_fourierInvCLM)))

end Internal

/-- The big-cell operator of the identity is the identity. -/
theorem bigCellOp_one : bigCellOp (1 : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) 0 0 1 = 1 := by
  simp [bigCellOp, chirp_zero, dilation_one, fourierCLM_mul_fourierInvCLM]

namespace Internal

theorem intertwinesAt_bigCellOp {A Ai B C D : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} (h : IsUnit Ai) (h1 : ∀ x, A (Ai x) = x) (h2 : ∀ x, Ai (A x) = x)
    (hAC : ∀ y z, ⟪A y, C z⟫ = ⟪C y, A z⟫) (hBD : ∀ y z, ⟪B y, D z⟫ = ⟪D y, B z⟫)
    (hAD : ∀ y z, ⟪A y, D z⟫ - ⟪C y, B z⟫ = ⟪y, z⟫) (c : ℝ) (p q : EuclideanSpace ℝ l) :
    IntertwinesAt (bigCellOp Ai B C c) p q (A p + B q) (C p + D q) := by
  have hS : ∀ x y, ⟪x, (C * Ai) y⟫ = ⟪y, (C * Ai) x⟫ := fun x y => by
    have := hAC (Ai x) (Ai y)
    rw [h1, h1] at this
    exact this.trans (real_inner_comm _ _)
  have hr : ∀ q x, ⟪D q - (C * Ai) (B q), x⟫ = ⟪q, Ai x⟫ := fun q x => by
    have := hAD (Ai x) q
    rw [h1] at this
    rw [inner_sub_left, real_inner_comm x, real_inner_comm x, hS, real_inner_comm (Ai x) q, ← this,
      real_inner_comm _ (B q)]
    rfl
  have hT : ∀ x y, ⟪x, (-(Ai * B)) y⟫ = ⟪y, (-(Ai * B)) x⟫ := fun x y => by
    simp only [_root_.neg_apply, inner_neg_right, mul_apply_eq_comp (f := Ai), ← hr,
      inner_sub_left]
    rw [← hBD, real_inner_comm (B x) (D y), real_inner_comm (B y), real_inner_comm (B x), hS]
  have e : C p + D q = D q - (C * Ai) (B q) + (C * Ai) (A p + B q) := by
    simp [h2, add_comm]
  rw [e]
  refine (intertwinesAt_chirp hS _ _).mul (((intertwinesAt_dilation h ?_ (hr q)).smul c).mul
    ((intertwinesAt_fourierCLM _ _).mul ((intertwinesAt_chirp hT _ _).mul (intertwinesAt_fourierInvCLM p q))))
  simp [h2, add_comm]

end Internal

end Real

end Langlands.Theta
