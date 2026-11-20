import Langlands.Representation.Archimedean.ComplexLocalCasimir
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # A fixed polynomial in the local coordinate square sum annihilates a standard vector -/

noncomputable section

open Filter Function Polynomial
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexLocalCasimir

open Langlands.LocalFactor.Archimedean
open ComplexDuality.LieInvariance (skewRe skewIm star_skewRe star_skewIm exp_smul_mem_unitaryGroup)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Std" => Automorphic.complexStandardKFinite n
local notation "ρ" => Whittaker.rightTranslation ℂ G
local notation "R" => rightDerivative (matrixModel ℂ n)

private def expCompact {X : M} (hX : X.conjTranspose = -X) (t : ℝ) : K :=
  ⟨Unitary.toUnits ⟨NormedSpace.exp (t • X), exp_smul_mem_unitaryGroup hX t⟩,
    exp_smul_mem_unitaryGroup hX t⟩

private theorem expCompact_zero {X : M} (hX : X.conjTranspose = -X) :
    (expCompact hX 0).val = 1 := by
  apply Units.ext
  change NormedSpace.exp ((0 : ℝ) • X) = 1
  simp

private theorem hasDerivAt_expCompact {X : M} (hX : X.conjTranspose = -X)
    {f : G → ℂ} (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (g : G) :
    HasDerivAt (fun t : ℝ => f (g * (expCompact hX t).val)) (R X f g) 0 := by
  let P (t : ℝ) := g * (expCompact hX t).val
  have h₀ : (P 0).val = g.val := by simp only [P, expCompact_zero, mul_one]
  have hpath : HasDerivAt (fun t : ℝ => (P t).val) (g.val * X) 0 := by
    change HasDerivAt (fun t : ℝ => g.val * NormedSpace.exp (t • X)) (g.val * X) 0
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).const_mul g.val
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using h
  rw [rightDerivative_eq_fderiv hf]
  have hF := (differentiableAt_unitsExtension hf g.isUnit).hasFDerivAt
  rw [← h₀] at hF
  simpa only [Function.comp_def, unitsExtension_val, h₀] using
    hF.comp_hasDerivAt (0 : ℝ) hpath

private theorem rightDerivative_mem_of_compactOrbit {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) {X : M} (hX : X.conjTranspose = -X)
    (S : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k : K, ρ k.val f ∈ S) (hfS : f ∈ S) :
    R X f ∈ S := by
  have hclosed := S.closed_of_finiteDimensional
  let slopeFun (t : ℝ) : G → ℂ := (↑t⁻¹ : ℂ) • (ρ (expCompact hX t).val f - f)
  have hlim : Tendsto slopeFun (𝓝[≠] (0 : ℝ)) (𝓝 (R X f)) := by
    apply tendsto_pi_nhds.mpr
    intro g
    have h := (hasDerivAt_expCompact hX hf g).tendsto_slope
    have heq : (fun t => slopeFun t g) =
        slope (fun t : ℝ => f (g * (expCompact hX t).val)) 0 := by
      funext t
      simp only [slopeFun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, slope_def_module, sub_zero,
        expCompact_zero, mul_one, Complex.real_smul]
      rfl
    rwa [heq]
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun t =>
    S.smul_mem _ (S.sub_mem (hS _) hfS))

private def compactOrbitSpan (f : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun k : K => ρ k.val f)

private theorem rightTranslate_mem_compactOrbitSpan {f v : G → ℂ}
    (hv : v ∈ compactOrbitSpan f) (k : K) : ρ k.val v ∈ compactOrbitSpan f := by
  have hle : compactOrbitSpan f ≤ (compactOrbitSpan f).comap (ρ k.val) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k₀, rfl⟩
    change ρ k.val (ρ k₀.val f) ∈ compactOrbitSpan f
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨k * k₀, rfl⟩
  exact hle hv

private theorem mem_compactOrbitSpan (f : G → ℂ) : f ∈ compactOrbitSpan f :=
  Submodule.subset_span ⟨1, by simp⟩

/-- The right-differential action of the sum of squares in the real matrix coordinates. -/
def coordinateSquareOperator (ds : List ComplexCharacterData) : Module.End ℂ (Std ds) :=
  envelopingAction (complexStandardLie n ds) (coordinateSquareSum n)

/-- A real Lie generator acts by the corresponding right derivative on the standard module. -/
theorem realGenerator_action (ds : List ComplexCharacterData) (X : M) (f : Std ds) :
    ((envelopingAction (complexStandardLie n ds) (realGenerator n X) f : Std ds) : G → ℂ) =
      R X f := by
  change ((envelopingAction (complexStandardLie n ds)
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) f : Std ds) : G → ℂ) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  exact principalSeriesLie_one_tmul_apply_coe ℂ n (complexPositionCharacter ds) X f

private theorem restrict_poly {E : Type*} [AddCommGroup E] [Module ℂ E] (T : Module.End ℂ E)
    (S : Submodule ℂ E) (hS : ∀ f ∈ S, T f ∈ S) (p : ℂ[X]) (v : S) :
    Polynomial.aeval T p v.val = (Polynomial.aeval (T.restrict hS) p v).val := by
  let T₀ := T.restrict hS
  have hpow (j : ℕ) (w : S) : (T ^ j) w.val = ((T₀ ^ j) w).val := by
    induction j generalizing w with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      exact ih (T₀ w)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, Submodule.coe_add]
  | monomial j c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    change c • (T ^ j) v.val = (c • ((T₀ ^ j) v)).val
    rw [hpow]
    rfl

private theorem exists_monic_of_invariant {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : Module.End ℂ E) (S : Submodule ℂ E) [FiniteDimensional ℂ S]
    (hS : ∀ f ∈ S, T f ∈ S) {v : E} (hv : v ∈ S) :
    ∃ p : ℂ[X], p.Monic ∧ Polynomial.aeval T p v = 0 := by
  let T₀ := T.restrict hS
  let w : S := ⟨v, hv⟩
  refine ⟨T₀.charpoly, T₀.charpoly_monic, ?_⟩
  change Polynomial.aeval T T₀.charpoly w.val = 0
  rw [restrict_poly T S hS, LinearMap.aeval_self_charpoly]
  rfl

/-! The restriction is finite dimensional because it lies in the compact orbit span. -/

/-- The coordinate square sum preserves a finite-dimensional subspace containing each
unitary-finite standard vector. -/
theorem exists_invariant_coordinateSquareOperator_submodule
    (ds : List ComplexCharacterData) (f : Std ds) :
    ∃ V : Submodule ℂ (Std ds), FiniteDimensional ℂ V ∧
      f ∈ V ∧ ∀ v ∈ V, coordinateSquareOperator ds v ∈ V := by
  let W := compactOrbitSpan (f : G → ℂ)
  let : FiniteDimensional ℂ W := f.property.2
  let V := W.comap (Automorphic.complexStandardKFinite n ds).subtype
  let i : V →ₗ[ℂ] W :=
    ((Automorphic.complexStandardKFinite n ds).subtype.comp V.subtype).codRestrict W
      (fun v => v.property)
  let : FiniteDimensional ℂ V := FiniteDimensional.of_injective i (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : W => (z : G → ℂ)) h)
  let A := envelopingAction (complexStandardLie n ds)
  have hder (X : M) (hX : X.conjTranspose = -X) (v : Std ds) (hv : v ∈ V) :
      A (realGenerator n X) v ∈ V := by
    change ((A (realGenerator n X) v : Std ds) : G → ℂ) ∈ W
    rw [show _ = R X (v : G → ℂ) from realGenerator_action ds X v]
    exact rightDerivative_mem_of_compactOrbit v.property.1.1 hX W
      (fun k => rightTranslate_mem_compactOrbitSpan hv k) hv
  have hcomp (v : Std ds) (hv : v ∈ V) : A (compactSquareSum n) v ∈ V := by
    rw [compactSquareSum]
    simp only [map_smul, map_sum, map_add, map_mul, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.add_apply, pow_two, Module.End.mul_apply]
    refine V.smul_mem _ (V.sum_mem fun a _ => V.sum_mem fun b _ => V.add_mem ?_ ?_)
    · have h := hder (skewRe a b) (by simpa only [Matrix.star_eq_conjTranspose] using star_skewRe a b)
      exact h _ (h _ hv)
    · have h := hder (skewIm a b) (by simpa only [Matrix.star_eq_conjTranspose] using star_skewIm a b)
      exact h _ (h _ hv)
  obtain ⟨c, hc⟩ := complexStandardLie_hasInfinitesimalCharacter n ds (matrixCasimir n)
    (matrixCasimir_mem_center n)
  let T := coordinateSquareOperator (n := n) ds
  have hT (v : Std ds) (hv : v ∈ V) : T v ∈ V := by
    change A (coordinateSquareSum n) v ∈ V
    rw [coordinateSquareSum_eq_casimir_add_compact, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply]
    change A (matrixCasimir n) v + (2 : ℂ) • A (compactSquareSum n) v ∈ V
    have hcv : A (matrixCasimir n) v = c • v :=
      congrArg (fun H : Module.End ℂ (Std ds) => H v) hc
    rw [hcv]
    exact V.add_mem (V.smul_mem c hv) (V.smul_mem _ (hcomp v hv))
  exact ⟨V, inferInstance, mem_compactOrbitSpan (f : G → ℂ), hT⟩

/-- Every unitary-finite standard vector is killed by a monic polynomial in
the right-coordinate square sum. -/
theorem exists_monic_coordinateSquareOperator_annihilator
    (ds : List ComplexCharacterData) (f : Std ds) :
    ∃ p : ℂ[X], p.Monic ∧ Polynomial.aeval (coordinateSquareOperator ds) p f = 0 := by
  obtain ⟨V, _, hf, hV⟩ := exists_invariant_coordinateSquareOperator_submodule ds f
  exact exists_monic_of_invariant (coordinateSquareOperator ds) V hV hf

end Langlands.Archimedean.ComplexLocalCasimir
