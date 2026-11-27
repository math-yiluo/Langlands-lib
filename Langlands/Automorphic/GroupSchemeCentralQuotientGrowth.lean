import Langlands.Automorphic.GroupSchemeCentralCurveAction
import Langlands.Global.AdelicCentralLogParameter
import Mathlib.Analysis.ODE.Gronwall

/-! # Uniform adelic growth from a fixed infinitesimal central ideal -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints
  Langlands.Geometry.Manifold Langlands.Algebra.SignedCartanCasimir RepresentationGrowth

private theorem norm_one_le_of_linearODE {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : V →L[ℂ] V) (f : ℝ → V) (hf : ∀ t, HasDerivAt f (D (f t)) t)
    (s : ℝ) (hs : ‖f 0‖ ≤ s) : ‖f 1‖ ≤ s * Real.exp ‖D‖ := by
  have h := dist_le_of_trajectories_ODE (v := fun _ => D) (K := ‖D‖₊)
    (a := 0) (b := 1) (δ := s) (g := fun _ => 0)
    (fun _ => D.lipschitzWith) (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (fun t _ => (hf t).hasDerivWithinAt) continuousOn_const
    (fun t _ => by simpa only [map_zero] using (hasDerivAt_const t (0 : V)).hasDerivWithinAt)
    (by simpa only [dist_zero_right] using hs) 1 ⟨zero_le_one, le_rfl⟩
  simpa only [dist_zero_right, sub_zero, mul_one, coe_nnnorm] using h

section CoordinateFunctionals

variable {R : Type*} [CommRing R] [Algebra ℂ R] {m : ℕ} (b : Module.Basis (Fin m) ℂ R)

private def basisEval : R →ₗ[ℂ] (Fin m → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, (b.coord i).smulRight (LinearMap.proj i)

private theorem basisEval_apply (z : R) (v : Fin m → ℂ) :
    basisEval b z v = ∑ i, b.repr z i * v i := by
  simp only [basisEval, LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem basisEval_values (φ : R →ₗ[ℂ] ℂ) (z : R) :
    basisEval b z (fun i => φ (b i)) = φ z := by
  rw [basisEval_apply]
  simpa only [map_sum, map_smul, smul_eq_mul] using congrArg φ (b.sum_repr z)

private def basisMultiplication : R →ₗ[ℂ] Module.End ℂ (Fin m → ℂ) where
  toFun z := LinearMap.pi fun i => basisEval b (z * b i)
  map_add' z w := by
    apply LinearMap.ext
    intro v
    funext i
    change basisEval b ((z + w) * b i) v = basisEval b (z * b i) v + basisEval b (w * b i) v
    simp only [add_mul, map_add, LinearMap.add_apply]
  map_smul' a z := by
    apply LinearMap.ext
    intro v
    funext i
    change basisEval b ((a • z) * b i) v = a • basisEval b (z * b i) v
    simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply]

end CoordinateFunctionals

/-- Bounds on finitely many fixed central derivatives on the norm-one subgroup control the
full function by a polynomial of uniform degree, for a prescribed cofinite center ideal. -/
def CentralQuotientGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (_hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsConnectedReductive G → IsClosedSubgroup rho →
    ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∃ (m : ℕ) (z : Fin m → AdelicEnvelopingCenter F G hsmooth) (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (f : FinitePlotSmoothRationalFunctions F G),
        (∀ w ∈ J, adelicCenterAction F G hsmooth hcalc w f = 0) →
        ∀ s : ℝ, 0 ≤ s →
        (∀ i, ∀ n : normOneSubgroup F G,
          ‖evaluate F G (adelicCenterAction F G hsmooth hcalc (z i) f).val n.val‖ ≤ s) →
        ∀ g : AdelicGroupPoints F G,
          ‖evaluate F G f.val g‖ ≤ C * adelicHeight F G rho g ^ k * s

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The action modulo the fixed ideal yields a finite system of linear differential equations
along the smooth logarithmic central paths. -/
theorem centralQuotientGrowth : CentralQuotientGrowthStatement.{u} := by
  classical
  intro F _ _ G _ N d rho hN hsmooth hcalc hG hρ J hJ
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let M := InfiniteAdelicGroupPoints F G
  let W := smoothModel F d
  let I := 𝓘(ℝ, W)
  let : LieGroup I (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  let A := AdelicGroupPoints F G
  let V : Type u := FinitePlotSmoothRationalFunctions F G
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let U := AdelicEnvelopingAlgebra F G hsmooth
  let Z := AdelicEnvelopingCenter F G hsmooth
  let Q := Z ⧸ J
  let q : Z →ₐ[ℂ] Q := Ideal.Quotient.mkₐ ℂ J
  have : Module.Finite ℂ Q := hJ
  let : Module.Free ℂ Q := Module.Free.of_divisionRing ℂ Q
  let m := Module.finrank ℂ Q
  let b : Module.Basis (Fin m) ℂ Q := Module.finBasis ℂ Q
  choose z hz using fun i => Ideal.Quotient.mk_surjective (b i)
  have hzq (i : Fin m) : q (z i) = b i := hz i
  let T := Fin m → ℂ
  obtain ⟨r, c, hc, hc₀, hcadd, hccent, cp, kp, hcp, hsplit⟩ :=
    PositiveRealTorus.centralLogParameter F G rho hsmooth hG hρ hN
  let P := ULift.{u} (Fin r) → ℝ
  let Iₚ := 𝓘(ℝ, P)
  let ray (x : P) (t : ℝ) := c (t • x)
  have hray (x : P) : ContMDiff 𝓘(ℝ, ℝ) I ∞ (ray x) :=
    hc.comp ((ContinuousLinearMap.toSpanSingleton ℝ x).contDiff.contMDiff)
  have hray₀ (x : P) : ray x 0 = 1 := by simp [ray, hc₀]
  have hrayAdd (x : P) (s t : ℝ) : ray x (s + t) = ray x s * ray x t := by
    change c ((s + t) • x) = c (s • x) * c (t • x)
    rw [add_smul, hcadd]
  let X : P →L[ℝ] W := mfderiv Iₚ I c 0
  have hX (x : P) : mfderiv 𝓘(ℝ, ℝ) I (ray x) 0 (1 : ℝ) = X x := by
    let L := ContinuousLinearMap.toSpanSingleton ℝ x
    change mfderiv 𝓘(ℝ, ℝ) I (c ∘ L) 0 (1 : ℝ) = _
    have hL : MDifferentiableAt 𝓘(ℝ, ℝ) Iₚ L 0 :=
      (L.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)
    rw [mfderiv_comp 0 (hc.mdifferentiableAt (by simp)) hL,
      mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    change (mfderiv Iₚ I c (L 0) : P →L[ℝ] W) (L 1) = X x
    rw [map_zero, ContinuousLinearMap.toSpanSingleton_apply_one]
    rfl
  let gen : P →ₗ[ℝ] U := (realGenerator (L := GroupLieAlgebra I M)).toLinearMap.comp X.toLinearMap
  have hgen (x : P) : gen x ∈ Z := by
    have h := centralCurveEnveloping F G hsmooth hG (ray x) (hray x) (hray₀ x)
      (fun t y => hccent (t • x) y)
    change realGenerator (L := GroupLieAlgebra I M) (mfderiv 𝓘(ℝ, ℝ) I (ray x) 0 (1 : ℝ)) ∈ Z at h
    rw [hX] at h
    exact h
  let ξ : P →ₗ[ℝ] Z := gen.codRestrict (Z.toSubmodule.restrictScalars ℝ) hgen
  let : NormedSpace ℝ (T →L[ℂ] T) := NormedSpace.restrictScalars ℝ ℂ _
  let B₀ : Z →ₗ[ℂ] T →L[ℂ] T := LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((basisMultiplication b).comp q.toLinearMap)
  let B : P →L[ℝ] T →L[ℂ] T := ((B₀.restrictScalars ℝ).comp ξ).toContinuousLinearMap
  let a := ⌈‖B‖⌉₊
  let R := (basisEval b (1 : Q)).toContinuousLinearMap
  refine ⟨m, z, (1 + ‖R‖) * cp ^ a, kp * a,
    mul_pos (by positivity) (pow_pos hcp _), ?_⟩
  intro f hf s hs hvals g
  let act := adelicCenterAction F G hsmooth hcalc
  let actQ : Q →ₗ[ℂ] V := (J.restrictScalars ℂ).liftQ (adelicCenterOrbitMap F G hsmooth hcalc f)
    (fun w hw => LinearMap.mem_ker.mpr (hf w hw))
  have hactQ (w : Z) : actQ (q w) = act w f := rfl
  have hactQ_mul (w : Z) (v : Q) : actQ (q w * v) = act w (actQ v) := by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    change actQ (q w * q v) = act w (actQ (q v))
    rw [← map_mul, hactQ, hactQ, map_mul, Module.End.mul_apply]
  let eval (a : A) : V →ₗ[ℂ] ℂ :=
    { toFun v := evaluate F G v.val a
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let ψ (a : A) := (eval a).comp actQ
  obtain ⟨x, n, hg, hx⟩ := hsplit g
  let path (t : ℝ) := n.val * ofInfinite F G (ray x t)
  have hPath (t : ℝ) : path t = pair F G (infinite F G n.val * ray x t) (finite F G n.val) := by
    calc
      _ = pair F G (infinite F G n.val) (finite F G n.val) * pair F G (ray x t) 1 := by
        rw [pair_projections, ← ofInfinite_eq_pair]
      _ = _ := by rw [pair_mul, mul_one]
  let Φ (t : ℝ) : T := fun i => ψ (path t) (b i)
  have hΦ (t : ℝ) : HasDerivAt Φ (B x (Φ t)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    let f' := actQ (b i)
    let arch := finitePlotSmoothSlice F G (finite F G n.val) f'
    have harch : ContMDiff I 𝓘(ℝ, ℂ) ∞ arch.val :=
      (isPlotSmooth_iff_contMDiff F G hsmooth _).mp arch.property
    have hd := hasDerivAt_mul_smoothOneParameter (ray x) (hray x) (hray₀ x) (hrayAdd x) _ harch
      (infinite F G n.val) t
    rw [hX] at hd
    have hv (t : ℝ) : Φ t i = arch.val (infinite F G n.val * ray x t) := by
      change evaluate F G f'.val (path t) = _
      rw [hPath, finitePlotSmoothSlice_apply]
    have hval : B x (Φ t) i = ψ (path t) (q (ξ x) * b i) := by
      change basisEval b (q (ξ x) * b i) (fun j => ψ (path t) (b j)) = _
      exact basisEval_values b _ _
    simp only [hv, hval]
    change HasDerivAt _ (evaluate F G (actQ (q (ξ x) * b i)).val (path t)) t
    rw [hactQ_mul, hPath]
    change HasDerivAt _ (evaluate F G (adelicEnvelopingAction F G hsmooth hcalc
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ]
        (X x : GroupLieAlgebra I M))) f').val
      (pair F G (infinite F G n.val * ray x t) (finite F G n.val))) t
    rw [finitePlotSmoothEnvelopingAction_real_generator, evaluate_finitePlotSmoothDifferentialAction]
    exact hd
  have hΦ₀ : ‖Φ 0‖ ≤ s := by
    apply (pi_norm_le_iff_of_nonneg hs).mpr
    intro i
    change ‖evaluate F G (actQ (b i)).val (path 0)‖ ≤ s
    have hn : path 0 = n.val := by
      change n.val * ofInfinite F G (ray x 0) = n.val
      rw [hray₀, map_one, mul_one]
    rw [hn, ← hzq i, hactQ]
    exact hvals i n
  have hΦ₁ := norm_one_le_of_linearODE (B x) Φ hΦ s hΦ₀
  have hg₁ : path 1 = g := by
    change n.val * ofInfinite F G (c (1 • x)) = g
    rw [one_smul, ← hg]
  have heval : evaluate F G f.val g = R (Φ 1) := by
    change eval g f = basisEval b (1 : Q) (fun i => ψ (path 1) (b i))
    rw [basisEval_values, hg₁]
    change eval g f = eval g (actQ 1)
    rw [← map_one q, hactQ, map_one, Module.End.one_apply]
  have hB : ‖B x‖ ≤ (a : ℝ) * ‖x‖ :=
    (B.le_opNorm x).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (norm_nonneg _))
  have hexp : Real.exp ‖B x‖ ≤ cp ^ a * adelicHeight F G rho g ^ (kp * a) := by
    calc
      _ ≤ Real.exp (‖x‖ * (a : ℝ)) := Real.exp_le_exp.mpr (by rwa [mul_comm])
      _ = Real.exp ‖x‖ ^ a := by rw [Real.exp_mul, Real.rpow_natCast]
      _ ≤ (cp * adelicHeight F G rho g ^ kp) ^ a :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hx a
      _ = _ := by rw [mul_pow, pow_mul]
  rw [heval]
  calc
    _ ≤ ‖R‖ * ‖Φ 1‖ := R.le_opNorm _
    _ ≤ (1 + ‖R‖) * (s * Real.exp ‖B x‖) :=
      mul_le_mul (le_add_of_nonneg_left zero_le_one) hΦ₁ (norm_nonneg _) (by positivity)
    _ ≤ (1 + ‖R‖) * (s * (cp ^ a * adelicHeight F G rho g ^ (kp * a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hs) (by positivity)
    _ = _ := by ring

end Langlands.Automorphic.GroupSchemeFunctions
