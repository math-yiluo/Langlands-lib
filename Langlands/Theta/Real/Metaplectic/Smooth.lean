import Langlands.Theta.Real.Metaplectic.Covering
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# Smoothness of the metaplectic representation and one-parameter subgroups

* `RealMetaplecticGroup.contDiff_weil_comp`: along a continuous family `γ : ℝᵏ → Mp` whose image in
  `Sp` is smooth, `t ↦ weil (γ t) f` is smooth for every Schwartz function `f` (near each point the
  Schwartz operator is the explicit big-cell operator, whose derivative is known).
* `RealMetaplecticGroup.oneParameter X`, for `X ∈ sp`: the lift through `1` of
  `t ↦ exp (t • X)`, the unique continuous one (`proj` is a covering map;
  `RealMetaplecticGroup.eq_oneParameter`). It is a one-parameter subgroup, and
  `t ↦ weil (oneParameter X t) f` has derivative `oscillatorDeriv X f` at `0`
  (`hasDerivAt_weil_oneParameter`): `oscillatorDeriv` is the derived representation.
* On Schwartz space the same holds weakly: `contDiff_weilSchwartz_comp`,
  `hasDerivAt_weilSchwartz_oneParameter`, for every continuous linear functional (which factors
  through `L²` norms of the Weyl algebra).
* `Intertwines.exists_generator_mem_weylAlgebra`: a weakly continuous one-parameter group of
  intertwiners along a one-parameter group of symplectic maps has an infinitesimal generator in the
  Weyl algebra (it is `oscillatorDeriv X` plus a scalar).
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform
open scoped Real ContDiff RealInnerProductSpace

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l] [DecidableEq l]
open Langlands.Theta.Real

namespace Real

namespace Internal

def orb {k : ℕ} (γ : (Fin k → ℝ) → RealMetaplecticGroup l) (f : RealSchwartz l) (t : Fin k → ℝ) : RealL2 l := RealMetaplecticGroup.weil (γ t) (schwartzToL2 l f)

def dm {k : ℕ} (γ : (Fin k → ℝ) → RealMetaplecticGroup l) (t : Fin k → ℝ) (a b : l ⊕ l) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ c, ((RealMetaplecticGroup.proj (γ t))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c • fderiv ℝ (fun t => (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) c b) t

theorem hasFDerivAt_orb {k : ℕ} (γ : (Fin k → ℝ) → RealMetaplecticGroup l)
    (hγ : Continuous γ) (hs : ∀ a b, Differentiable ℝ fun t => (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) (f : RealSchwartz l)
    (t₀ : Fin k → ℝ) :
    HasFDerivAt (orb γ f)
      (∑ a, ∑ b, (dm γ t₀ a b).smulRight (orb γ (bigCellSectionDeriv (Matrix.single a b 1) f) t₀)) t₀ := by
  have hh : Continuous fun t => (γ t₀)⁻¹ * γ t := continuous_const.mul hγ
  have hev : ∀ᶠ t in 𝓝 t₀, RealMetaplecticGroup.weilSchwartz ((γ t₀)⁻¹ * γ t) = bigCellSection (RealMetaplecticGroup.proj ((γ t₀)⁻¹ * γ t)).1 := by
    have h1 : Tendsto (fun t => (γ t₀)⁻¹ * γ t) (𝓝 t₀) (𝓝 1) := by
      have := hh.tendsto t₀
      rwa [inv_mul_cancel] at this
    exact h1.eventually RealMetaplecticGroup.eventually_weilSchwartz_eq_bigCellSection
  let m : (Fin k → ℝ) → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => (RealMetaplecticGroup.proj ((γ t₀)⁻¹ * γ t)).1
  have hm : ∀ t, m t = ((RealMetaplecticGroup.proj (γ t₀))⁻¹ : Matrix.symplecticGroup l ℝ).1 * (RealMetaplecticGroup.proj (γ t)).1 := fun t => by
    show (RealMetaplecticGroup.proj ((γ t₀)⁻¹ * γ t)).1 = _
    rw [map_mul, map_inv]
    rfl
  have hm1 : m t₀ = 1 := by
    show (RealMetaplecticGroup.proj ((γ t₀)⁻¹ * γ t₀)).1 = 1
    rw [inv_mul_cancel, map_one]
    rfl
  have hmd : ∀ a b, HasFDerivAt (fun t => m t a b) (dm γ t₀ a b) t₀ := by
    intro a b
    have e : (fun t => m t a b) = fun t => ∑ c, ((RealMetaplecticGroup.proj (γ t₀))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c * (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) c b := by
      funext t
      rw [hm t, Matrix.mul_apply]
    rw [e]
    have := HasFDerivAt.sum (u := Finset.univ) (x := t₀) fun c _ =>
      ((hs c b t₀).hasFDerivAt).const_mul (((RealMetaplecticGroup.proj (γ t₀))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c)
    have e2 : (fun t => ∑ c, ((RealMetaplecticGroup.proj (γ t₀))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c * (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) c b) =
        ∑ c, fun t => ((RealMetaplecticGroup.proj (γ t₀))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c * (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) c b := by
      funext t
      simp [Finset.sum_apply]
    rw [e2]
    exact this
  have hsec := hasFDerivAt_bigCellSection (Fin k → ℝ) m (dm γ t₀) t₀ hm1 hmd f
  let L : RealL2 l →L[ℝ] RealL2 l :=
    ((RealMetaplecticGroup.weil (γ t₀)).toContinuousLinearEquiv.toContinuousLinearMap : RealL2 l →L[ℂ] RealL2 l).restrictScalars ℝ
  have hL : ∀ v, L v = RealMetaplecticGroup.weil (γ t₀) v := fun v => rfl
  have h2 := L.hasFDerivAt.comp t₀ hsec
  have heq : orb γ f =ᶠ[𝓝 t₀] (⇑L ∘ fun x => schwartzToL2 l (bigCellSection (m x) f)) := by
    filter_upwards [hev] with t ht
    calc orb γ f t = RealMetaplecticGroup.weil (γ t₀ * ((γ t₀)⁻¹ * γ t)) (schwartzToL2 l f) := by
          rw [mul_inv_cancel_left]; rfl
      _ = RealMetaplecticGroup.weil (γ t₀) (RealMetaplecticGroup.weil ((γ t₀)⁻¹ * γ t) (schwartzToL2 l f)) := by rw [map_mul]; rfl
      _ = RealMetaplecticGroup.weil (γ t₀) (schwartzToL2 l (RealMetaplecticGroup.weilSchwartz ((γ t₀)⁻¹ * γ t) f)) := by rw [RealMetaplecticGroup.Internal.weil_toLp_aux]
      _ = _ := by rw [ht]; rfl
  have h3 := h2.congr_of_eventuallyEq heq
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  simp only [hL, orb]

theorem contDiff_dm {k : ℕ} (γ : (Fin k → ℝ) → RealMetaplecticGroup l)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) (a b : l ⊕ l) (n : ℕ) :
    ContDiff ℝ n fun t => dm γ t a b := by
  have hinv : ∀ a c, ContDiff ℝ ∞ fun t => ((RealMetaplecticGroup.proj (γ t))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c := by
    intro a c
    have e : (fun t => ((RealMetaplecticGroup.proj (γ t))⁻¹ : Matrix.symplecticGroup l ℝ).1 a c) =
        fun t => ∑ e, (∑ d, (-J l ℝ) a d * (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) e d) * J l ℝ e c := by
      funext t
      show ((-J l ℝ) * (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * J l ℝ) a c = _
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [e]
    exact ContDiff.sum fun e _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs e d)).mul contDiff_const
  have hn : ((n : WithTop ℕ∞)) ≤ ∞ := by exact_mod_cast le_top
  have hn1 : ((n : WithTop ℕ∞)) + 1 ≤ ∞ := by exact_mod_cast le_top
  unfold dm
  exact ContDiff.sum fun c _ => ((hinv a c).of_le hn).smul ((hs c b).fderiv_right hn1)

end Internal

end Real

namespace RealMetaplecticGroup

/-- Smoothness along smooth families: if `γ` is continuous and `proj ∘ γ` is smooth, then
`t ↦ weil (γ t) f` is smooth for every Schwartz function `f`. -/
theorem contDiff_weil_comp {k : ℕ} {γ : (Fin k → ℝ) → RealMetaplecticGroup l} (hγ : Continuous γ)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)
    (f : RealSchwartz l) : ContDiff ℝ ∞ fun t => weil (γ t) (f.toLp 2) := by
  have hd : ∀ a b, Differentiable ℝ fun t => (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b := fun a b =>
    (hs a b).differentiable (by simp)
  suffices H : ∀ n : ℕ, ∀ g : RealSchwartz l, ContDiff ℝ n (orb γ g) from contDiff_infty.2 fun n => H n f
  intro n
  induction n with
  | zero =>
    intro g
    have := (contDiff_zero (𝕜 := ℝ) (f := orb γ g)).2 ((RealMetaplecticGroup.continuous_weil (schwartzToL2 l g)).comp hγ)
    exact_mod_cast this
  | succ n ih =>
    intro g
    have key := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := orb γ g) (n := n)).2
      ⟨fun t => ∑ a, ∑ b, (dm γ t a b).smulRight (orb γ (bigCellSectionDeriv (Matrix.single a b 1) g) t),
        ContDiff.sum fun a _ => ContDiff.sum fun b _ => (contDiff_dm γ hs a b n).smulRight (ih _),
        fun t => hasFDerivAt_orb γ hγ hd g t⟩
    exact_mod_cast key

end RealMetaplecticGroup

namespace Real

/-- The exponential of an element of `sp` is symplectic. -/
theorem exp_mem_symplecticGroup {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    NormedSpace.exp X ∈ Matrix.symplecticGroup l ℝ := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [SymplecticGroup.mem_iff', Matrix.mul_assoc]
  exact h2

/-- A matrix whose exponentials `exp (t • X)` are all symplectic lies in `sp`. -/
theorem mem_sp_of_exp_mem_symplecticGroup (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  let : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0:ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᵀ)) (NormedSpace.exp ((0:ℝ) • Xᵀ) * Xᵀ) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᵀ 0
  have h3 := (h1.mul_const (Matrix.J l ℝ)).mul h2
  have h4 : ((fun t : ℝ => NormedSpace.exp (t • X) * Matrix.J l ℝ) * fun t : ℝ => NormedSpace.exp (t • Xᵀ)) =
      fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.mem_iff.1 (h t)
    rw [← Matrix.exp_transpose, Matrix.transpose_smul] at this
    exact this
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0:ℝ) (Matrix.J l ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h5
  have hJ := Matrix.J_squared l ℝ
  have h6 : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X) := by
    have h7 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = 0 := by
      rw [h5]; simp
    have h8 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ
        = Matrix.J l ℝ * X * (Matrix.J l ℝ * Matrix.J l ℝ) +
          (Matrix.J l ℝ * Matrix.J l ℝ) * Xᵀ * Matrix.J l ℝ := by
      noncomm_ring
    rw [h8, hJ] at h7
    simp only [mul_neg, mul_one, neg_mul, one_mul] at h7 ⊢
    rw [← neg_add, neg_eq_zero] at h7
    exact eq_neg_of_add_eq_zero_right h7
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact h6

namespace Internal

/-- The path `t ↦ exp (t • X)` in `Sp_{2l}(ℝ)`. -/
def expPath (X : LieAlgebra.Symplectic.sp l ℝ) : C(ℝ, Matrix.symplecticGroup l ℝ) :=
  ⟨fun t => ⟨NormedSpace.exp (t • X.1), exp_mem_symplecticGroup (SMulMemClass.smul_mem t X.2)⟩,
    (continuous_pi fun a => continuous_pi fun b => continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X.1 t).continuousAt).subtype_mk _⟩

theorem expPath_apply (X : LieAlgebra.Symplectic.sp l ℝ) (t : ℝ) :
    (expPath X t).1 = NormedSpace.exp (t • X.1) := rfl

theorem existsUnique_lift (X : LieAlgebra.Symplectic.sp l ℝ) :
    ∃! Γ : C(ℝ, RealMetaplecticGroup l), Γ 0 = 1 ∧ ⇑RealMetaplecticGroup.proj ∘ ⇑Γ = ⇑(expPath X) :=
  IsCoveringMap.existsUnique_continuousMap_lifts (RealMetaplecticGroup.isCoveringMap_proj (l := l))
    (expPath X) 0 1
    (by rw [map_one]; exact Subtype.ext (by simp [expPath_apply]))

end Internal

end Real

namespace RealMetaplecticGroup

/-- The lift of `t ↦ exp (t • X)` through `1`, for `X ∈ sp`: the unique continuous lift. -/
def oneParameter (X : LieAlgebra.Symplectic.sp l ℝ) : ℝ → RealMetaplecticGroup l :=
  ⇑(existsUnique_lift X).exists.choose

/-- The one-parameter subgroup is continuous. -/
theorem continuous_oneParameter (X : LieAlgebra.Symplectic.sp l ℝ) :
    Continuous (oneParameter X) :=
  (existsUnique_lift X).exists.choose.continuous

/-- `oneParameter X 0 = 1`. -/
@[simp] theorem oneParameter_zero (X : LieAlgebra.Symplectic.sp l ℝ) : oneParameter X 0 = 1 :=
  (existsUnique_lift X).exists.choose_spec.1

/-- `oneParameter X` lies over `t ↦ exp (t • X)`. -/
theorem proj_oneParameter (X : LieAlgebra.Symplectic.sp l ℝ) (t : ℝ) :
    (proj (oneParameter X t)).1 = NormedSpace.exp (t • X.1) :=
  congrArg Subtype.val (congrFun (existsUnique_lift X).exists.choose_spec.2 t)

/-- Uniqueness: a continuous lift of `t ↦ exp (t • X)` through `1` is `oneParameter X`. -/
theorem eq_oneParameter (X : LieAlgebra.Symplectic.sp l ℝ) {γ : ℝ → RealMetaplecticGroup l}
    (hc : Continuous γ) (h0 : γ 0 = 1) (hp : ∀ t, (proj (γ t)).1 = NormedSpace.exp (t • X.1)) :
    γ = oneParameter X := by
  have := (existsUnique_lift X).unique (y₁ := ⟨γ, hc⟩) ⟨h0, funext fun t => Subtype.ext (hp t)⟩
    (existsUnique_lift X).exists.choose_spec
  exact congrArg DFunLike.coe this

/-- `oneParameter X` is a one-parameter subgroup. -/
theorem oneParameter_add (X : LieAlgebra.Symplectic.sp l ℝ) (s t : ℝ) :
    oneParameter X (s + t) = oneParameter X s * oneParameter X t := by
  have hpr : ∀ t, proj (oneParameter X t) = expPath X t := fun t => Subtype.ext (proj_oneParameter X t)
  have hpadd : ∀ s t, expPath X (s + t) = expPath X s * expPath X t := fun s t => Subtype.ext (by
    show NormedSpace.exp ((s + t) • X.1) = NormedSpace.exp (s • X.1) * NormedSpace.exp (t • X.1)
    rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X.1).smul_left s).smul_right t)])
  have := IsCoveringMap.eq_of_comp_eq (isCoveringMap_proj (l := l)) (g₁ := fun t => oneParameter X (s + t))
    (g₂ := fun t => oneParameter X s * oneParameter X t)
    ((continuous_oneParameter X).comp (continuous_const.add continuous_id))
    (continuous_const.mul (continuous_oneParameter X))
    (funext fun t => by simp only [Function.comp, map_mul, hpr, hpadd]) 0 (by simp)
  exact congrFun this t

/-- The derivative at `0` of the Weil representation along `oneParameter X` is the infinitesimal
oscillator operator of `X`. -/
theorem hasDerivAt_weil_oneParameter (X : LieAlgebra.Symplectic.sp l ℝ) (f : RealSchwartz l) :
    HasDerivAt (fun t => weil (oneParameter X t) (f.toLp 2)) ((oscillatorDeriv X.1 f).toLp 2) 0 := by
  have hpr : ∀ t, proj (oneParameter X t) = expPath X t := fun t => Subtype.ext (proj_oneParameter X t)
  have h3' : ∀ᶠ g in 𝓝 (oneParameter X 0), weilSchwartz g = bigCellSection (proj g).1 := by
    rw [oneParameter_zero]; exact eventually_weilSchwartz_eq_bigCellSection
  have hev := ((continuous_oneParameter X).tendsto 0).eventually h3'
  have hd : ∀ a b, HasFDerivAt (fun x : ℝ => NormedSpace.exp (x • X.1) a b)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X.1 a b)) 0 := fun a b => by
    have := hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ a b) X.1 0
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, Matrix.entryLinearMap_apply] at this
    exact this.hasFDerivAt
  have hS := (hasFDerivAt_bigCellSection ℝ (fun x => NormedSpace.exp (x • X.1))
    (fun a b => (1 : ℝ →L[ℝ] ℝ).smulRight (X.1 a b)) 0 (by simp) hd f).hasDerivAt
  have hval : (∑ a, ∑ b, ((1 : ℝ →L[ℝ] ℝ).smulRight (X.1 a b)).smulRight
      (schwartzToL2 l (bigCellSectionDeriv (Matrix.single a b 1) f))) 1 = (oscillatorDeriv X.1 f).toLp 2 := by
    simp only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul]
    rw [show oscillatorDeriv X.1 f = bigCellSectionDeriv X.1 f from oscillatorDeriv_eq X.2 f, ← qd_sum X.1 f]
    show _ = schwartzToL2 l _
    simp only [map_sum, ContinuousLinearMap.map_smul_of_tower]
  rw [hval] at hS
  refine hS.congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  show weil (oneParameter X t) (schwartzToL2 l f) = _
  rw [Internal.weil_toLp_aux, ht, hpr t]
  rfl

end RealMetaplecticGroup

namespace Real

namespace Internal

open RealMetaplecticGroup

theorem toLp_dRho_omS
    (A : RealSchwartz l →L[ℂ] RealSchwartz l) (g : RealMetaplecticGroup l)
    (w : l ⊕ l → ℝ) (f : RealSchwartz l) :
    schwartzToL2 l ((A * schrodingerDeriv w) (RealMetaplecticGroup.weilSchwartz g f)) = ∑ a,
      (((-(Matrix.J l ℝ * (RealMetaplecticGroup.proj g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) a : ℂ) •
        schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz g (schrodingerDeriv (Pi.single a 1) f))) := by
  have h1 : (RealMetaplecticGroup.proj g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ
      ((-(Matrix.J l ℝ * (RealMetaplecticGroup.proj g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) = w := by
    rw [mulVec_mulVec, mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      SymplecticGroup.mem_iff.1 (RealMetaplecticGroup.proj g).2, J_squared, neg_neg, one_mulVec]
  rw [mul_apply_eq_comp]
  conv_lhs => rw [← h1, ← RealMetaplecticGroup.weilSchwartz_schrodingerDeriv, schrodingerDeriv_eq_sum]
  simp only [_root_.sum_apply, _root_.smul_apply, map_sum, map_smul]

theorem contDiff_toLp_omS
   
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → RealMetaplecticGroup l}
    (hγ : ∀ a b, ContDiff ℝ ∞ fun t => (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)
    (h5 : ∀ f : RealSchwartz l, ContDiff ℝ ∞ fun t => RealMetaplecticGroup.weil (γ t) (f.toLp 2 volume)) {A : RealSchwartz l →L[ℂ] RealSchwartz l} (hA : A ∈ weylAlgebra l)
    (f : RealSchwartz l) : ContDiff ℝ ∞ fun t => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz (γ t) f)) := by
  revert f
  refine weylAlgebra_induction (P := fun A => ∀ f, ContDiff ℝ ∞ fun t => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz (γ t) f))) ?_ ?_ ?_ ?_ ?_ hA
  · intro f
    simpa only [RealMetaplecticGroup.weil_toLp, one_apply_eq_self, SchwartzMap.toLpCLM_apply] using h5 f
  · intro A w ih f
    simp only [toLp_dRho_omS, coe_smul]
    refine ContDiff.sum fun a _ => ContDiff.fun_smul ?_ (ih _)
    simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
    exact ContDiff.sum fun b _ => ContDiff.mul (ContDiff.neg (ContDiff.sum fun c _ => ContDiff.mul
      (ContDiff.sum fun d _ => contDiff_const.mul (hγ _ _)) contDiff_const)) contDiff_const
  · intro f
    simp only [_root_.zero_apply]
    exact contDiff_const
  · intro A B hA hB f
    simp only [_root_.add_apply, map_add]
    exact (hA f).add (hB f)
  · intro c A hA f
    simp only [_root_.smul_apply, map_smul]
    exact (hA f).const_smul c

theorem hasDerivAt_exp_apply (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (a b : l ⊕ l) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  let := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ a b)).hasFDerivAt.comp_hasDerivAt 0 h

theorem hasDerivAt_toLp_omS
   
    {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) {γ : ℝ → RealMetaplecticGroup l} (h0 : γ 0 = 1)
    (hγ : ∀ t, (RealMetaplecticGroup.proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X))
    (h6 : ∀ f : RealSchwartz l, HasDerivAt (fun t => RealMetaplecticGroup.weil (γ t) (f.toLp 2 volume)) ((oscillatorDeriv X f).toLp 2 volume) 0)
    {A : RealSchwartz l →L[ℂ] RealSchwartz l} (hA : A ∈ weylAlgebra l) (f : RealSchwartz l) :
    HasDerivAt (fun t => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz (γ t) f))) (schwartzToL2 l (A (oscillatorDeriv X f))) 0 := by
  revert f
  refine weylAlgebra_induction
    (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz (γ t) f))) (schwartzToL2 l (A (oscillatorDeriv X f))) 0) ?_ ?_ ?_ ?_ ?_ hA
  · intro f
    simpa only [RealMetaplecticGroup.weil_toLp, one_apply_eq_self, SchwartzMap.toLpCLM_apply] using h6 f
  · intro A w ih f
    simp only [toLp_dRho_omS, hγ, coe_smul]
    have hJ : Matrix.J l ℝ * Xᵀ * Matrix.J l ℝ = X := by
      have h := mul_J_symm hX
      rw [transpose_mul, J_transpose, neg_mul, neg_eq_iff_eq_neg] at h
      rw [h, neg_mul, Matrix.mul_assoc, J_squared]
      simp
    have hd : ∀ a, HasDerivAt
        (fun t : ℝ => ((-(Matrix.J l ℝ * (NormedSpace.exp (t • X))ᵀ * Matrix.J l ℝ)) *ᵥ w) a) (-(X *ᵥ w) a) 0 := by
      intro a
      conv => enter [2]; rw [← hJ]
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply, ← Finset.sum_neg_distrib,
        ← neg_mul]
      exact HasDerivAt.fun_sum fun b _ => HasDerivAt.mul_const (HasDerivAt.fun_sum fun c _ => HasDerivAt.mul_const
        (HasDerivAt.fun_sum fun d _ => (hasDerivAt_exp_apply X _ _).const_mul _) _) _
    refine (HasDerivAt.fun_sum fun a _ => (hd a).fun_smul (ih (schrodingerDeriv (Pi.single a 1) f))).congr_deriv ?_
    have e : schrodingerDeriv w * oscillatorDeriv X = oscillatorDeriv X * schrodingerDeriv w - schrodingerDeriv (X *ᵥ w) := by
      rw [← oscillatorDeriv_commutator hX, sub_sub_cancel]
    rw [mul_apply_eq_comp, ← mul_apply_eq_comp (schrodingerDeriv w), e, schrodingerDeriv_eq_sum w,
      schrodingerDeriv_eq_sum (X *ᵥ w)]
    simp only [_root_.sum_apply, _root_.smul_apply, map_sum,
      map_smul, zero_smul, NormedSpace.exp_zero, transpose_one, mul_one, J_squared, neg_neg, one_mulVec,
      h0, map_one, one_apply_eq_self, _root_.sub_apply, mul_apply_eq_comp,
      map_sub, neg_smul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
    simp only [coe_smul]
    rfl
  · intro f
    simp only [_root_.zero_apply, map_zero]
    exact hasDerivAt_const _ _
  · intro A B hA hB f
    simp only [_root_.add_apply, map_add]
    exact (hA f).add (hB f)
  · intro c A hA f
    simp only [_root_.smul_apply, map_smul]
    exact (hA f).const_smul c

end Internal

end Real

namespace RealMetaplecticGroup

/-- Weak smoothness on Schwartz space along smooth families. -/
theorem contDiff_weilSchwartz_comp (lam : RealSchwartz l →L[ℂ] ℂ) {k : ℕ}
    {γ : (Fin k → ℝ) → RealMetaplecticGroup l} (hc : Continuous γ)
    (hγ : ∀ a b, ContDiff ℝ ∞ fun t => (proj (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)
    (f : RealSchwartz l) : ContDiff ℝ ∞ fun t => lam (weilSchwartz (γ t) f) := by
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor_through_toLp lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).contDiff.comp
    (contDiff_pi.2 fun i => contDiff_toLp_omS hγ (contDiff_weil_comp hc hγ) (hA i) f)

/-- The weak derivative on Schwartz space along `oneParameter X` is `oscillatorDeriv X`. -/
theorem hasDerivAt_weilSchwartz_oneParameter (X : LieAlgebra.Symplectic.sp l ℝ) (f : RealSchwartz l)
    (lam : RealSchwartz l →L[ℂ] ℂ) :
    HasDerivAt (fun t => lam (weilSchwartz (oneParameter X t) f)) (lam (oscillatorDeriv X.1 f)) 0 := by
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor_through_toLp lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_pi.2 fun i => hasDerivAt_toLp_omS X.2 (oneParameter_zero X) (proj_oneParameter X)
      (hasDerivAt_weil_oneParameter X) (hA i) f)

end RealMetaplecticGroup

namespace Real

namespace Internal

open RealMetaplecticGroup

theorem exists_lift {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    ∃ (U : ℝ → RealSchwartz l →L[ℂ] RealSchwartz l) (Q : RealSchwartz l →L[ℂ] RealSchwartz l),
      Q ∈ weylAlgebra l ∧
      (∀ f, U 0 f = f) ∧ (∀ s t f, U (s + t) f = U s (U t f)) ∧
      (∀ t, Intertwines (fun w => NormedSpace.exp (t • X) *ᵥ w) (U t).toLinearMap) ∧
      (∀ f, Continuous fun t => (U t f).toLp 2 volume) ∧
      ∀ f (lam : RealSchwartz l →L[ℂ] ℂ), HasDerivAt (fun t => lam (U t f)) (lam (Q f)) 0 := by
  let Xs : LieAlgebra.Symplectic.sp l ℝ := ⟨X, hX⟩
  have h0 : oneParameter Xs 0 = 1 := oneParameter_zero Xs
  have hm : ∀ s t, oneParameter Xs (s + t) = oneParameter Xs s * oneParameter Xs t :=
    oneParameter_add Xs
  have hγ : ∀ t, (proj (oneParameter Xs t)).1 = NormedSpace.exp (t • X) := proj_oneParameter Xs
  refine ⟨fun t => weilSchwartz (oneParameter Xs t), oscillatorDeriv X, oscillatorDeriv_mem_weylAlgebra X,
    fun f => by simp [h0], fun s t f => by simp [hm],
    fun t => Intertwines.of_rhoFun (fun f => ?_) (fun w f g hg => ?_), fun f => ?_,
    fun f lam => hasDerivAt_weilSchwartz_oneParameter Xs f lam⟩
  · show ‖(weilSchwartz (oneParameter Xs t) f).toLp 2 volume‖ = _
    rw [← weil_toLp, LinearIsometryEquiv.norm_map]
  · obtain ⟨g', hg'⟩ := exists_schwartz_eq_rhoFun (NormedSpace.exp (t • X) *ᵥ w)
      (weilSchwartz (oneParameter Xs t) f)
    have : weilSchwartz (oneParameter Xs t) g = g' := by
      apply injective_toLp 2 volume
      show (weilSchwartz (oneParameter Xs t) g).toLp 2 volume = g'.toLp 2 volume
      rw [← weil_toLp, toLp_eq_schrodingerL2 hg, toLp_eq_schrodingerL2 hg', weil_schrodingerL2, hγ,
        weil_toLp]
    exact this ▸ hg'
  · simp only [← weil_toLp]
    exact (continuous_weil _).comp (continuous_oneParameter Xs)

end Internal

/-- A weakly continuous one-parameter group of intertwiners along a one-parameter group of
symplectic linear maps has an infinitesimal generator in the Weyl algebra. -/
theorem Intertwines.exists_generator_mem_weylAlgebra (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', stdSymplecticForm l ℝ (s t w) (s t w') = stdSymplecticForm l ℝ w w') (S : ℝ → RealSchwartz l →ₗ[ℂ] RealSchwartz l) (hS : ∀ t, Intertwines (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : RealSchwartz l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlgebra l, ∀ f (lam : RealSchwartz l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by
  have ss' : ∀ t w w', sympl (s t w) (s t w') = sympl w w' := fun t w w' => by
    simp only [sympl_eq_stdSymplecticForm]; exact ss t w w'
  have hm : ∃ X : Matrix (l ⊕ l) (l ⊕ l) ℝ, ∀ t, LinearMap.toMatrix' (s t) = NormedSpace.exp (t • X) := by
    let := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
    let := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
    have : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
    refine exists_exp_smul_of_continuous_oneParameter (fun t => LinearMap.toMatrix' (s t)) ?_ ?_ fun t u => ?_
    · refine continuous_matrix fun a b => ?_
      simp only [LinearMap.toMatrix'_apply]
      exact (continuous_apply a).comp (sc _)
    · rw [show s 0 = LinearMap.id from LinearMap.ext s0, LinearMap.toMatrix'_id]
    · rw [show s (t + u) = s t ∘ₗ s u from LinearMap.ext (sm t u), LinearMap.toMatrix'_comp]
  obtain ⟨X, hX⟩ := hm
  have hs : ∀ t w, s t w = NormedSpace.exp (t • X) *ᵥ w := fun t w => by rw [← hX, LinearMap.toMatrix'_mulVec]
  have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
    refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
    show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X)
    ext a b
    have h1 : ∀ t : ℝ, ∑ i, ∑ j, NormedSpace.exp (t • X) i a * (Matrix.J l ℝ i j * NormedSpace.exp (t • X) j b) =
        Matrix.J l ℝ a b := fun t => by
      have := ss' t (Pi.single a 1) (Pi.single b 1)
      rw [sympl_eq, sympl_eq, neg_inj, hs, hs] at this
      simpa [dotProduct, mulVec, Finset.mul_sum, Pi.single_apply, mul_add] using this
    have h2 : HasDerivAt (fun t : ℝ => ∑ i, ∑ j, NormedSpace.exp (t • X) i a *
        (Matrix.J l ℝ i j * NormedSpace.exp (t • X) j b)) _ 0 :=
      HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
        (hasDerivAt_exp_apply X i a).fun_mul ((hasDerivAt_exp_apply X j b).const_mul _)
    simp only [h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    simp only [zero_smul, NormedSpace.exp_zero, Finset.sum_add_distrib, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero] at h3
    simp only [Matrix.mul_apply, transpose_apply, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    linarith
  obtain ⟨U, Q, hQ, U0, Um, Ui, Uc, Ud⟩ := exists_lift hsp
  have hc : ∀ t, ∃ c : ℂ, ∀ f, S t f = c • U t f := fun t => by
    have hi : Intertwines id (S t ∘ₗ (U (-t)).toLinearMap) := Intertwines.of_rhoFun
      (fun f => ((hS t).norm_toLp _).trans ((Ui (-t)).norm_toLp f)) fun w f g hg => by
        have := (hS t).comm_rhoFun _ _ _ ((Ui (-t)).comm_rhoFun w f g hg)
        rw [← hs, ← sm, add_neg_cancel, s0] at this
        exact this
    obtain ⟨c, hc⟩ := hi.exists_eq_smul fun f => ⟨U t (S (-t) f), by
      show S t (U (-t) (U t _)) = f
      rw [← Um, neg_add_cancel, U0, ← Sm, add_neg_cancel, S0]⟩
    refine ⟨c, fun f => ?_⟩
    rw [← hc]
    show _ = S t (U (-t) (U t f))
    rw [← Um, neg_add_cancel, U0]
  choose c hc using hc
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have hφ0 : φ ≠ 0 := fun h => hφ (by simp [h])
  have hU : ∀ t, U t φ ≠ 0 := fun t h => hφ0 (by rw [← U0 φ, ← neg_add_cancel t, Um, h, map_zero])
  have c0 : c 0 = 1 := by
    have := hc 0 φ
    rw [S0, U0] at this
    exact (smul_left_injective ℂ hφ0 (this.symm.trans (one_smul _ _).symm))
  have cm : ∀ t u, c (t + u) = c t * c u := fun t u => by
    have := Sm t u φ
    rw [hc, hc, hc, map_smul, smul_smul, ← Um] at this
    exact smul_left_injective ℂ (hU _) this
  have cc : Continuous c := continuous_iff_continuousAt.2 fun t₀ => by
    let lam : RealSchwartz l →L[ℂ] ℂ := (innerSL ℂ ((U t₀ φ).toLp 2 volume)).comp (schwartzToL2 l)
    have h1 : Continuous fun t => lam (U t φ) := (innerSL ℂ ((U t₀ φ).toLp 2 volume)).continuous.comp (Uc φ)
    have h2 : lam (U t₀ φ) ≠ 0 := fun h => hU t₀ (by
      apply injective_toLp 2 volume
      have : (U t₀ φ).toLp 2 volume = 0 := inner_self_eq_zero.1 h
      exact this.trans (map_zero (schwartzToL2 l)).symm)
    refine ((Sc φ lam).continuousAt.div h1.continuousAt h2).congr ?_
    filter_upwards [h1.continuousAt.eventually_ne h2] with t ht
    simp only [Pi.div_apply, hc, map_smul, smul_eq_mul]
    rw [mul_div_cancel_right₀ _ ht]
  obtain ⟨z, hz⟩ := exists_exp_smul_of_continuous_oneParameter c cc c0 cm
  have hd : HasDerivAt c z 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) z (0 : ℝ)
    simp only [← hz, c0, one_mul] at this
    exact this
  refine ⟨z • 1 + Q, add_mem (Subalgebra.smul_mem _ (one_mem _) _) hQ, fun f lam => ?_⟩
  simp only [hc, map_smul, smul_eq_mul]
  refine (hd.fun_mul (Ud f lam)).congr_deriv ?_
  simp [c0, U0]

end Real

end Langlands.Theta
