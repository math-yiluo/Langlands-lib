import Langlands.Representation.Archimedean.RealStandardCompactTrace

/-! # A compact kernel formula for the real standard averaging trace -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactAverage

open OrthogonalFinitePolynomial RealPrincipalSeriesDuality

local notation "G" => Langlands.GeneralLinear
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "V" => fun n ds => kFiniteFunctions (realStandardModule n ds)
  (unitaryCompact ℝ n)

variable {n : ℕ}

private theorem compactRestriction_mem (ds : List RealBlock) (f : V n ds) :
    (fun k : K n => f.1 (Unitary.toUnits k)) ∈ polynomialFunctions n := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_kFiniteVectors
    (continuous_of_mem_kFiniteFunctions f.2) f.2.2 (1 : G n ℝ)
  change _ ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (entry n ij : K n → ℂ))
  rw [Algebra.adjoin_range_eq_range_aeval]
  refine ⟨P, funext fun k => ?_⟩
  have h := MvPolynomial.comp_aeval (R := ℂ) (fun ij : Fin n × Fin n =>
    (entry n ij : K n → ℂ)) (Pi.evalAlgHom ℂ (fun _ : K n => ℂ) k)
  have he := congrArg (fun ψ => ψ P) h
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at he
  change (MvPolynomial.aeval (fun ij : Fin n × Fin n => (entry n ij : K n → ℂ)) P) k = _
  rw [he, ← one_mul (Unitary.toUnits k), hP k]
  rfl

/-- Restriction of the actual compact-finite standard module to polynomial functions on `O(n)`. -/
def compactRestriction (ds : List RealBlock) : V n ds →ₗ[ℂ] polynomialFunctions n where
  toFun f := ⟨fun k => f.1 (Unitary.toUnits k), compactRestriction_mem ds f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem exists_separated_sum {h : K n → K n → ℂ} (hh : h ∈ separated n) :
    ∃ (m : ℕ) (a : Fin m → polynomialFunctions n) (b : Fin m → C(K n, ℂ)),
      ∀ x y, h x y = ∑ i, (a i : K n → ℂ) x * b i y := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨a, ha, b, rfl⟩ := hh
    exact ⟨1, fun _ => ⟨a, ha⟩, fun _ => b, fun x y => by simp⟩
  | zero =>
    exact ⟨0, Fin.elim0, Fin.elim0, fun _ _ => by simp⟩
  | add h h' _ _ ih ih' =>
    obtain ⟨m, a, b, hab⟩ := ih
    obtain ⟨p, c, d, hcd⟩ := ih'
    refine ⟨m + p, Fin.addCases a c, Fin.addCases b d, fun x y => ?_⟩
    simp [Fin.sum_univ_add, hab, hcd]
  | smul z h _ ih =>
    obtain ⟨m, a, b, hrep⟩ := ih
    refine ⟨m, fun i => z • a i, b, fun x y => ?_⟩
    change z * h x y = ∑ i, (z * (a i : K n → ℂ) x) * b i y
    rw [hrep, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

private theorem cutoff_separated (φ : polynomialStar n) :
    (fun x y : K n => (φ : C(K n, ℂ)) (x⁻¹ * y)) ∈ separated n := by
  have hφ : (φ : C(K n, ℂ)) ∈ (polynomialStar n).toSubalgebra := φ.2
  rw [polynomialStar_toSubalgebra] at hφ
  exact inv_mul_mem_separated hφ

/-- The polynomial column `x ↦ φ(x⁻¹ y)` of the compact convolution kernel. -/
def kernelColumn (φ : polynomialStar n) (y : K n) : polynomialFunctions n :=
  ⟨fun x => (φ : C(K n, ℂ)) (x⁻¹ * y), by
    obtain ⟨m, a, b, h⟩ := exists_separated_sum (cutoff_separated φ)
    have heq : (fun x => (φ : C(K n, ℂ)) (x⁻¹ * y)) =
        ∑ i, b i y • (a i : K n → ℂ) := by
      funext x
      rw [h]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq]
    exact (polynomialFunctions n).toSubmodule.sum_mem fun i _ =>
      (polynomialFunctions n).toSubmodule.smul_mem (b i y) (a i).2⟩

private theorem polynomial_sum_apply {ι : Type*} [Fintype ι] (a : ι → polynomialFunctions n)
    (c : ι → ℂ) (x : K n) :
    ((∑ i, c i • a i : polynomialFunctions n) : K n → ℂ) x =
      ∑ i, c i * (a i : K n → ℂ) x := by
  change ((polynomialFunctions n).val (∑ i, c i • a i)) x = _
  simp only [map_sum, Finset.sum_apply]
  rfl

private theorem trace_range_eq_sum {X ι : Type*} [AddCommGroup X] [Module ℂ X] [Fintype ι]
    (A : Module.End ℂ X) [FiniteDimensional ℂ A.range] (a : ι → X) (ℓ : ι → X →ₗ[ℂ] ℂ)
    (h : ∀ x, A x = ∑ i, ℓ i x • a i) :
    LinearMap.trace ℂ A.range (A.rangeRestrict.comp A.range.subtype) = ∑ i, ℓ i (a i) := by
  let S := Submodule.span ℂ (Set.range a)
  have hS : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
  have ha (i : ι) : a i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have hle : A.range ≤ S := by
    rintro _ ⟨x, rfl⟩
    rw [h]
    exact S.sum_mem fun i _ => S.smul_mem _ (ha i)
  let I : A.range →ₗ[ℂ] S := Submodule.inclusion hle
  let Q : S →ₗ[ℂ] A.range := A.rangeRestrict.comp S.subtype
  have hQS : I.comp Q = ∑ i, ((ℓ i).comp S.subtype).smulRight ⟨a i, ha i⟩ := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change A (x : X) = _
    simpa only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smulRight_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_smul] using h (x : X)
  calc
    _ = LinearMap.trace ℂ S (I.comp Q) :=
      LinearMap.trace_comp_comm' (R := ℂ) (M := A.range) (N := S) I Q
    _ = _ := by rw [hQS, map_sum]; simp

variable (μ : Measure (K n)) [hμ : μ.IsHaarMeasure]

private def integralTest (ds : List RealBlock) (g : G n ℝ) (b : C(K n, ℂ)) :
    V n ds →ₗ[ℂ] ℂ := by
  have hi (f : V n ds) :
      Integrable (fun y => b y * f.1 (Unitary.toUnits y * g)) μ :=
    OrthogonalFinitePolynomial.integrable_of_continuous μ
      (b.continuous.mul ((continuous_of_mem_kFiniteFunctions f.2).comp
        (continuous_unitary_toUnits.mul continuous_const)))
  exact
    { toFun := fun f => ∫ y, b y * f.1 (Unitary.toUnits y * g) ∂μ
      map_add' := fun f h => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hi f) (hi h)
      map_smul' := fun z f => by
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun _ => by ring }

/-- The range trace is the integral obtained by applying a left inverse of compact restriction
to the kernel columns and evaluating at the right translate by `g`. -/
theorem averageTrace_eq_kernelIntegral (ds : List RealBlock) (φ : polynomialStar n)
    (g : G n ℝ) (P : polynomialFunctions n →ₗ[ℂ] V n ds)
    (hP : ∀ f, P (compactRestriction ds f) = f) :
    averageTrace μ ds φ g =
      ∫ y, (P (kernelColumn φ y)).1 (Unitary.toUnits y * g) ∂μ := by
  obtain ⟨m, a, b, hab⟩ := exists_separated_sum (cutoff_separated φ)
  have hi (i : Fin m) (f : V n ds) :
      Integrable (fun y => b i y * f.1 (Unitary.toUnits y * g)) μ :=
    OrthogonalFinitePolynomial.integrable_of_continuous μ
      ((b i).continuous.mul ((continuous_of_mem_kFiniteFunctions f.2).comp
        (continuous_unitary_toUnits.mul continuous_const)))
  have hA (f : V n ds) : compactRestriction ds (averageMap μ ds φ g f) =
      ∑ i, integralTest μ ds g (b i) f • a i := by
    apply Subtype.ext
    funext x
    change (∫ y, (φ : C(K n, ℂ)) y * f.1 (Unitary.toUnits x * Unitary.toUnits y * g) ∂μ) = _
    have hshift := integral_mul_left_eq_self (μ := μ) (fun y : K n =>
      (φ : C(K n, ℂ)) (x⁻¹ * y) * f.1 (Unitary.toUnits y * g)) x
    simp only [inv_mul_cancel_left, map_mul] at hshift
    rw [hshift, polynomial_sum_apply]
    simp_rw [hab, Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      change (∫ y, ((a i : K n → ℂ) x * b i y) * f.1 (Unitary.toUnits y * g) ∂μ) =
        (∫ y, b i y * f.1 (Unitary.toUnits y * g) ∂μ) * (a i : K n → ℂ) x
      rw [← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun _ => by ring)
    · exact fun i _ => ((hi i f).const_mul ((a i : K n → ℂ) x)).congr
        (ae_of_all _ fun _ => mul_assoc _ _ _ |>.symm)
  have hA' (f : V n ds) :
      averageMap μ ds φ g f = ∑ i, integralTest μ ds g (b i) f • P (a i) := by
    rw [← hP (averageMap μ ds φ g f), hA, map_sum]
    simp [map_smul]
  have hcol (y : K n) : kernelColumn φ y = ∑ i, b i y • a i := by
    apply Subtype.ext
    funext x
    change (φ : C(K n, ℂ)) (x⁻¹ * y) = _
    rw [polynomial_sum_apply, hab]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  calc
    averageTrace μ ds φ g = ∑ i, integralTest μ ds g (b i) (P (a i)) :=
      trace_range_eq_sum (averageMap μ ds φ g) (fun i => P (a i))
        (fun i => integralTest μ ds g (b i)) hA'
    _ = ∫ y, ∑ i, b i y * (P (a i)).1 (Unitary.toUnits y * g) ∂μ :=
      (integral_finsetSum _ (fun i _ => hi i (P (a i)))).symm
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [hcol, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The compact averaging trace has a column integral formula for any linear left inverse of
the polynomial compact restriction. -/
def RealStandardCompactTraceKernelStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (K n)) [μ.IsHaarMeasure] (ds : List RealBlock)
    (φ : polynomialStar n) (g : G n ℝ) (P : polynomialFunctions n →ₗ[ℂ] V n ds),
    (∀ f, P (compactRestriction ds f) = f) →
    averageTrace μ ds φ g =
      ∫ y, (P (kernelColumn φ y)).1 (Unitary.toUnits y * g) ∂μ

omit hμ in
theorem realStandardCompactTraceKernel : RealStandardCompactTraceKernelStatement :=
  fun _ μ _ ds φ g P hP => averageTrace_eq_kernelIntegral μ ds φ g P hP

end Langlands.Archimedean.RealStandardCompactAverage
