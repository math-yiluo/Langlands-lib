import Langlands.Global.RankinSelberg.RealBruhatRootStabilizer
import Langlands.Group.GL.RealBruhatProductChart
import Langlands.HarmonicAnalysis.Distribution.SmoothChartVectorField

/-! # Nilpotence of the simple-root action on the Bruhat normal space -/

noncomputable section

open Filter Set Langlands.GeneralLinear Langlands.GeneralLinear.RealBruhatProductChart
open Langlands.HarmonicAnalysis
open scoped ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBruhatNormalAction

open RealBruhatRootStabilizer

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => upperUnipotent (r + 1) ℝ

/-- The ambient derivative of the paired matrix action. -/
def ambientGenerator (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) : M →L[ℝ] M :=
  (LinearMap.mulLeft ℝ (leftGenerator b w i) +
    LinearMap.mulRight ℝ (rightGenerator v i)).toContinuousLinearMap

/-- The ambient generator expressed in the product coordinates at `(x,0)`. -/
def chartGenerator (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (x : Tangent w) : (Tangent w × Normal w) →L[ℝ] (Tangent w × Normal w) :=
  let e := productChart w
  (fderiv ℝ e.symm (e (x, 0))).comp
    ((ambientGenerator b v w i).comp (fderiv ℝ e (x, 0)))

/-- The transverse component of the chart generator. -/
def normalGenerator (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (x : Tangent w) : Normal w →L[ℝ] Normal w :=
  (ContinuousLinearMap.snd ℝ (Tangent w) (Normal w)).comp
    ((chartGenerator b v w i x).comp (ContinuousLinearMap.inr ℝ (Tangent w) (Normal w)))

private def rootAction (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (t : ℝ) : M →L[ℝ] M :=
  ContinuousLinearMap.mulLeftRight ℝ M (leftUnit b w i t).val (rightUnit v i t).val.val

private theorem rootAction_chart_tangent (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1)))
    (i : Fin r) (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w)
    (hg : productChart w (x, 0) = (b.val * permutation (r + 1) ℝ w * v.val).val)
    (u : Tangent w) (t : ℝ) :
    (fderiv ℝ (productChart w).symm (productChart w (x, 0))
      (rootAction b v w i t (fderiv ℝ (productChart w) (x, 0) (u, 0)))).2 = 0 := by
  let e := productChart w
  let H := rootAction b v w i t
  let y := e (x, 0)
  let c (s : ℝ) : Tangent w × Normal w := (x, 0) + s • ((u, 0) : Tangent w × Normal w)
  have hx' : (x, 0) ∈ e.source := ⟨hx, mem_univ _⟩
  have hy : y ∈ e.target := e.map_source hx'
  have hfix : H y = y := by
    rw [show y = (b.val * permutation (r + 1) ℝ w * v.val).val from hg]
    exact congrArg Units.val (leftUnit_mul_cell_mul_rightUnit b v w i t)
  have hc : HasDerivAt c (u, 0) 0 := by
    simpa only [c, id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const ((u, 0) : Tangent w × Normal w)).const_add (x, 0))
  have hc₀ : c 0 = (x, 0) := by simp [c]
  have hd := ((contDiffOn_productChart w).contDiffAt (e.open_source.mem_nhds hx')).differentiableAt (by simp)
  have hdi := ((contDiffOn_productChart_symm w).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have h₁ : HasDerivAt (fun s => e (c s)) (fderiv ℝ e (x, 0) (u, 0)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc hc₀.symm
  have h₂ := H.hasFDerivAt.comp_hasDerivAt 0 h₁
  have h₀ : y = H (e (c 0)) := by rw [hc₀, ← hfix]
  have h₃ := hdi.hasFDerivAt.comp_hasDerivAt_of_eq 0 h₂ h₀
  let S := ContinuousLinearMap.snd ℝ (Tangent w) (Normal w)
  have h₄ := S.hasFDerivAt.comp_hasDerivAt 0 h₃
  have hzero : (fun s => (e.symm (H (e (c s)))).2) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    have hcSource : ∀ᶠ s in 𝓝 (0 : ℝ), c s ∈ e.source :=
      hc.continuousAt (e.open_source.mem_nhds (hc₀.symm ▸ hx'))
    filter_upwards [hcSource] with s hs
    have hunit := isUnit_of_mem_productChart_target w (e.map_source hs)
    let g₀ : G := hunit.unit
    have hg₀ : g₀.val = e (c s) := IsUnit.unit_spec _
    have hg₀T : g₀.val ∈ e.target := hg₀ ▸ e.map_source hs
    have hg₀C : g₀ ∈ upperBruhatCell (r + 1) ℝ w := by
      apply (mem_cell_iff_normal_eq_zero w hg₀T).2
      rw [hg₀, e.left_inv hs]
      simp [c]
    let l : B := ⟨leftUnit b w i t, (leftUnit_mem_upper b w i hi t).1⟩
    let q : B := ⟨(rightUnit v i t).val, (rightUnit v i t).property.1⟩
    have hC := mem_upperBruhatCell_mul (r + 1) ℝ w q
      (mul_mem_upperBruhatCell (r + 1) ℝ w l hg₀C)
    have hT := mem_productChart_target_of_mem_cell w hC
    have hZ := (mem_cell_iff_normal_eq_zero w hT).1 hC
    change (e.symm ((l.val * g₀ * q.val).val)).2 = 0 at hZ
    simp only [Units.val_mul, hg₀] at hZ
    exact hZ
  exact h₄.unique ((hasDerivAt_const (0 : ℝ) (0 : Normal w)).congr_of_eventuallyEq hzero)

/-- The paired root derivative has no normal component on a tangent input. -/
theorem chartGenerator_tangent (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1)))
    (i : Fin r) (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w)
    (hg : productChart w (x, 0) = (b.val * permutation (r + 1) ℝ w * v.val).val)
    (u : Tangent w) : (chartGenerator b v w i x (u, 0)).2 = 0 := by
  let e := productChart w
  let X := fderiv ℝ e (x, 0) (u, 0)
  let T := (ContinuousLinearMap.snd ℝ (Tangent w) (Normal w)).comp
    (fderiv ℝ e.symm (e (x, 0)))
  have hd := T.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pairedAction b v w i X)
  have hzero : (fun t => T (rootAction b v w i t X)) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 :=
    Eventually.of_forall (rootAction_chart_tangent b v w i hi x hx hg u)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : Normal w)).congr_of_eventuallyEq hzero)

private theorem isNilpotent_of_intertwines_surj {A C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup C] [Module ℝ C] {f : Module.End ℝ A} {g : Module.End ℝ C}
    (p : A →ₗ[ℝ] C) (hp : Function.Surjective p) (h : ∀ x, p (f x) = g (p x))
    (hf : IsNilpotent f) : IsNilpotent g := by
  have hpow (k : ℕ) (x : A) : p ((f ^ k) x) = (g ^ k) (p x) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, LinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hp y
  simpa only [hk, LinearMap.zero_apply, map_zero] using (hpow k x).symm

/-- The nilpotent ambient infinitesimal action descends to the normal coordinates. -/
theorem normalGenerator_isNilpotent (b : B) (v : U) (w : Equiv.Perm (Fin (r + 1)))
    (i : Fin r) (hi : w i.castSucc < w i.succ) (x : Tangent w) (hx : x ∈ tangentDomain w)
    (hg : productChart w (x, 0) = (b.val * permutation (r + 1) ℝ w * v.val).val) :
    IsNilpotent (normalGenerator b v w i x).toLinearMap := by
  let e := productChart w
  let y := e (x, 0)
  let J := fderiv ℝ e (x, 0)
  let J' := fderiv ℝ e.symm y
  have hx' : (x, 0) ∈ e.source := ⟨hx, mem_univ _⟩
  have hy : y ∈ e.target := e.map_source hx'
  have hleft (z : Tangent w × Normal w) : J' (J z) = z :=
    fderiv_chart_symm_apply_fderiv (contDiffOn_productChart w) (contDiffOn_productChart_symm w) hx' z
  have hright (z : M) : J (J' z) = z := by
    have h := fderiv_chart_symm_apply_fderiv (e := e.symm)
      (contDiffOn_productChart_symm w) (contDiffOn_productChart w) hy z
    rw [e.left_inv hx'] at h
    exact h
  have hnil : IsNilpotent (chartGenerator b v w i x).toLinearMap := by
    apply isNilpotent_of_intertwines_surj J'.toLinearMap (fun z => ⟨J z, hleft z⟩) _
      (isNilpotent_pairedGenerator b v w i)
    intro z
    change J' (ambientGenerator b v w i z) = J' (ambientGenerator b v w i (J (J' z)))
    rw [hright]
  let S := ContinuousLinearMap.snd ℝ (Tangent w) (Normal w)
  apply isNilpotent_of_intertwines_surj S.toLinearMap (fun z => ⟨(0, z), rfl⟩) _ hnil
  intro z
  let T := chartGenerator b v w i x
  have hz : z = (z.1, 0) + (0, z.2) := by ext <;> simp
  have he : (T z).2 = (T (z.1, 0)).2 + (T (0, z.2)).2 := by
    conv_lhs => rw [hz]
    rw [map_add, Prod.snd_add]
  change (T z).2 = (T (0, z.2)).2
  rw [he, chartGenerator_tangent b v w i hi x hx hg, zero_add]

/-- At a lower-cell point the infinitesimal paired root action preserves the
tangent subspace and induces a nilpotent linear map on the normal coordinates. -/
def RealBruhatNormalActionStatement : Prop :=
  ∀ (r : ℕ) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r), w i.castSucc < w i.succ →
    ∀ (b : upperTriangularSubgroup (r + 1) ℝ) (v : upperUnipotent (r + 1) ℝ)
      (x : Tangent w), x ∈ tangentDomain w →
    productChart w (x, 0) = (b.val * permutation (r + 1) ℝ w * v.val).val →
    (∀ u : Tangent w, (chartGenerator b v w i x (u, 0)).2 = 0) ∧
      IsNilpotent (normalGenerator b v w i x).toLinearMap

theorem realBruhatNormalAction : RealBruhatNormalActionStatement := by
  intro r w i hi b v x hx hg
  exact ⟨chartGenerator_tangent b v w i hi x hx hg,
    normalGenerator_isNilpotent b v w i hi x hx hg⟩

end Langlands.Global.RankinSelbergGlobal.RealBruhatNormalAction
