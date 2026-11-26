import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Order.Interval.Set.Infinite

/-! # Descent of real Whittaker coefficients across a finite-dimensional kernel -/

noncomputable section

open Metric Set Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealLocalWhittaker

open RealIwasawa RealWhittakerGauge

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "D" => rightDerivative (matrixModel ℝ (r + 1))
local notation "V" ds => Automorphic.realStandardKFinite (r + 1) ds

private theorem conjRoot_scaled (g : G) (i : Fin r) (t : ℝ) :
    conjRoot (torus (Pi.single i.castSucc t) * g) i = Real.exp (-t) • conjRoot g i := by
  let y : Fin (r + 1) → ℝ := Pi.single i.castSucc t
  have hInv : ((torus y * g)⁻¹ : G).val = g⁻¹.val * Matrix.diagonal (fun j => Real.exp (-y j)) := by
    rw [mul_inv_rev, ← torus_neg, Units.val_mul, torus_val]
    rfl
  ext p q
  rw [Matrix.smul_apply, smul_eq_mul, conjRoot_apply, conjRoot_apply, hInv,
    Units.val_mul, torus_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hi : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ (i := i)).ne'
  simp only [y, Pi.single_eq_same, Pi.single_eq_of_ne hi, Real.exp_zero, one_mul]
  ring

private def derivativeOn {a : ℝˣ} (A : Submodule ℂ (G → ℂ)) (hA : A ≤ regularFunctions r a)
    (X : Mat) (hD : ∀ W ∈ A, D X W ∈ A) : Module.End ℂ A where
  toFun W := ⟨D X W.val, hD W.val W.property⟩
  map_add' W U := Subtype.ext (rightDerivative_add (hA W.property).2.1 (hA U.property).2.1 X)
  map_smul' c W := Subtype.ext (rightDerivative_smul (hA W.property).2.1 c X)

/-- A finite-dimensional space of regular nondegenerate Whittaker functions, invariant under
all matrix right derivatives, is zero. -/
theorem eq_bot_of_finiteDimensional_derivativeInvariant (hr : 0 < r) {a : ℝˣ}
    (A : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ A] (hA : A ≤ regularFunctions r a)
    (hD : ∀ (X : Mat) (W : G → ℂ), W ∈ A → D X W ∈ A) : A = ⊥ := by
  refine le_bot_iff.mp (fun W hW => ?_)
  rw [Submodule.mem_bot]
  funext g
  change W g = 0
  by_contra! hWg
  let i : Fin r := ⟨0, hr⟩
  let g' (t : ℝ) := torus (Pi.single i.castSucc t) * g
  let T := derivativeOn A hA (conjRoot g i) (hD (conjRoot g i))
  let S : Module.End ℂ (Module.Dual ℂ A) :=
    { toFun := fun e => e.comp T
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  let ev (t : ℝ) : Module.Dual ℂ A := (LinearMap.proj (g' t)).comp A.subtype
  let c : ℂ := 2 * Real.pi * (a : ℝ) * Complex.I
  have hc : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr a.ne_zero)) Complex.I_ne_zero
  let eigen (t : ℝ) : ℂ := (Real.exp t : ℝ) * c
  have hEig (t : ℝ) : S (ev t) = eigen t • ev t := by
    apply LinearMap.ext
    intro v
    have hd := rightDerivative_conjRoot (hA v.property) (g' t) i
    rw [show conjRoot (g' t) i = Real.exp (-t) • conjRoot g i from conjRoot_scaled g i t,
      rightDerivative_smul_left] at hd
    change (Real.exp (-t) : ℂ) * D (conjRoot g i) v.val (g' t) = c * v.val (g' t) at hd
    change D (conjRoot g i) v.val (g' t) = eigen t * v.val (g' t)
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-t)))
    rw [hd, ← mul_assoc]
    dsimp only [eigen]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  have ht : Continuous (fun t : ℝ => Pi.single i.castSucc t : ℝ → Fin (r + 1) → ℝ) := by
    apply continuous_pi
    intro j
    by_cases hj : j = i.castSucc
    · subst j
      simp only [Pi.single_eq_same]
      fun_prop
    · simpa only [Pi.single_eq_of_ne hj] using
        (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  have hCont : Continuous (fun t : ℝ => W (g' t)) :=
    (hA hW).2.1.continuous.comp ((continuous_torus.comp ht).mul continuous_const)
  have hg₀ : g' 0 = g := by simp [g', Pi.single_zero, torus_zero]
  have hOpen : IsOpen {t : ℝ | W (g' t) ≠ 0} := isOpen_ne.preimage hCont
  have hmem : (0 : ℝ) ∈ {t : ℝ | W (g' t) ≠ 0} := by
    change W (g' 0) ≠ 0
    rwa [hg₀]
  obtain ⟨δ, hδ, hNZ⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hmem)
  have hHas (t : Ioo (-δ) δ) : S.HasEigenvalue (eigen t) := by
    have hne : ev t ≠ 0 := by
      intro he
      have hz : W (g' t) = 0 := congrArg (fun f : Module.Dual ℂ A => f ⟨W, hW⟩) he
      have htδ : (t : ℝ) ∈ ball (0 : ℝ) δ := by
        rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
        exact t.property
      exact hNZ htδ hz
    exact S.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hEig t), hne⟩)
  let f : Ioo (-δ) δ → {μ : ℂ // S.HasEigenvalue μ} := fun t => ⟨eigen t, hHas t⟩
  have hf : Function.Injective f := by
    intro t q he
    apply Subtype.ext
    have h : eigen t = eigen q := congrArg Subtype.val he
    exact Real.exp_injective (Complex.ofReal_injective (mul_right_cancel₀ hc h))
  let _ : Finite {μ : ℂ // S.HasEigenvalue μ} := (S.finite_hasEigenvalue).to_subtype
  have hFinite : Finite (Ioo (-δ) δ) := Finite.of_injective f hf
  exact (Ioo_infinite (show -δ < δ by linarith)).not_finite (Set.finite_coe_iff.mp hFinite)

/-- A surjective standard-module intertwiner with a finite-dimensional kernel preserves
the exact coefficient space in the direction of descent in every rank greater than one. -/
def RealWhittakerFiniteKernelDescentStatement : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (ds es : List RealBlock) (a : ℝˣ),
    ∀ T : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] Automorphic.realStandardKFinite (r + 1) es,
      Function.Surjective T →
      IsRealStandardIntertwiner (r + 1) (realStandardRep (r + 1) es) (realStandardLie (r + 1) es) ds T →
      FiniteDimensional ℂ (LinearMap.ker T) →
      realWhittakerModel r ds a ≤ realWhittakerModel r es a

theorem model_le_of_finiteKernel (hr : 0 < r) {ds es : List RealBlock} (a : ℝˣ)
    (T : (V ds) →ₗ[ℂ] V es) (hTs : Function.Surjective T)
    (hT : IsRealStandardIntertwiner (r + 1) (realStandardRep (r + 1) es) (realStandardLie (r + 1) es) ds T)
    (hDim : FiniteDimensional ℂ (LinearMap.ker T)) :
    realWhittakerModel r ds a ≤ realWhittakerModel r es a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  let A := (LinearMap.ker T).map B
  let _ : FiniteDimensional ℂ (LinearMap.ker T) := hDim
  let _ : FiniteDimensional ℂ A := inferInstance
  have hA : A ≤ regularFunctions r a := by
    rintro W ⟨f, hf, rfl⟩
    exact ⟨hB.1 f, hB.2.1 f, HasPolynomialGrowth.of_bound (hB.2.2.1 f)⟩
  have hStable (X : Mat) (W : G → ℂ) (hW : W ∈ A) : D X W ∈ A := by
    obtain ⟨f, hf, rfl⟩ := hW
    obtain ⟨hf', hTf'⟩ := hT.2 X f
    let f' : V ds := ⟨D X f.val, hf'⟩
    have hKer : T f' = 0 := by rw [hTf', LinearMap.mem_ker.mp hf, map_zero]
    exact ⟨f', LinearMap.mem_ker.mpr hKer, hB.2.2.2.2 X f f' rfl⟩
  have hZero := eq_bot_of_finiteDimensional_derivativeInvariant hr A hA hStable
  have hKer : LinearMap.ker T ≤ LinearMap.ker B := by
    intro f hf
    have hb : B f ∈ A := ⟨f, hf, rfl⟩
    rw [hZero, Submodule.mem_bot] at hb
    exact LinearMap.mem_ker.mpr hb
  let B' := (T.liftOfSurjective hTs) ⟨B, hKer⟩
  have hComp (f : V ds) : B' (T f) = B f := T.equivOfSurjective_apply hTs hKer
  have hB' : IsRealWhittakerIntertwiner r es a B' := by
    constructor
    · intro F
      obtain ⟨f, rfl⟩ := hTs F
      rw [hComp]
      exact hB.1 f
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro F
      obtain ⟨f, rfl⟩ := hTs F
      rw [hComp]
      exact hB.2.1 f
    · intro F
      obtain ⟨f, rfl⟩ := hTs F
      rw [hComp]
      exact hB.2.2.1 f
    · intro k F F' hF'
      obtain ⟨f, rfl⟩ := hTs F
      obtain ⟨hf', hTf'⟩ := hT.1 k f
      let f' : V ds := ⟨_, hf'⟩
      have hEq : T f' = F' := by
        apply Subtype.ext
        rw [hTf', realStandardRep_apply_coe]
        have hk : Unitary.toUnits (⟨k.val.val, k.property⟩ :
            Matrix.unitaryGroup (Fin (r + 1)) ℝ) = k.val := Units.ext rfl
        rw [hk]
        exact hF'.symm
      rw [← hEq, hComp, hComp]
      exact hB.2.2.2.1 k f f' rfl
    · intro X F F' hF'
      obtain ⟨f, rfl⟩ := hTs F
      obtain ⟨hf', hTf'⟩ := hT.2 X f
      let f' : V ds := ⟨_, hf'⟩
      have hEq : T f' = F' := by
        apply Subtype.ext
        rw [hTf', realStandardLie_one_tmul_apply_coe]
        exact hF'.symm
      rw [← hEq, hComp, hComp]
      exact hB.2.2.2.2 X f f' rfl
  rintro W ⟨f, rfl⟩
  exact Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨T f, hComp f⟩)

theorem realWhittakerFiniteKernelDescent : RealWhittakerFiniteKernelDescentStatement :=
  fun _ hr _ _ a T hTs hT hDim => model_le_of_finiteKernel hr a T hTs hT hDim

end Langlands.Global.RankinSelbergGlobal.RealLocalWhittaker
