import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Integration in finite-dimensional algebraic coefficient spaces
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Module

universe uX uA uB uI

variable {X : Type uX} [MeasurableSpace X] (μ : Measure X)
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]

/-- Scalar integrability of an algebraic vector-valued function. -/
def IsScalarIntegrable (f : X → A) : Prop :=
  ∀ L : A →ₗ[ℂ] ℂ, Integrable (fun x => L (f x)) μ

/-- Integrate the coordinates of a finite basis; no topology on the coefficient
space is imposed. -/
def basisCoefficientIntegral {ι : Type uI} [Fintype ι] (b : Basis ι ℂ A)
    (f : X → A) : A :=
  ∑ i, (∫ x, b.repr (f x) i ∂μ) • b i

/-- Every linear scalar evaluation commutes with coefficient integration. -/
theorem basisCoefficientIntegral_linear_eval {ι : Type uI} [Fintype ι]
    (b : Basis ι ℂ A) {f : X → A} (hf : IsScalarIntegrable μ f)
    (L : A →ₗ[ℂ] ℂ) :
    L (basisCoefficientIntegral μ b f) = ∫ x, L (f x) ∂μ := by
  have hexp (x : X) : L (f x) = ∑ i, b.repr (f x) i * L (b i) := by
    conv_lhs => rw [← b.sum_repr (f x)]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [basisCoefficientIntegral, map_sum, map_smul, smul_eq_mul]
  simp_rw [hexp]
  have hcoord (i : ι) : Integrable (fun x => b.repr (f x) i) μ := by
    simpa only [Basis.coord_apply] using hf (b.coord i)
  rw [integral_finsetSum Finset.univ (fun i _ => (hcoord i).mul_const (L (b i)))]
  simp only [integral_mul_const]

/-- The result is independent of the chosen finite basis. -/
theorem basisCoefficientIntegral_eq {ι : Type uI} [Fintype ι]
    {κ : Type*} [Fintype κ] (b : Basis ι ℂ A) (c : Basis κ ℂ A)
    {f : X → A} (hf : IsScalarIntegrable μ f) :
    basisCoefficientIntegral μ b f = basisCoefficientIntegral μ c f := by
  apply c.ext_elem
  intro i
  exact (basisCoefficientIntegral_linear_eval μ b hf (c.coord i)).trans
    (basisCoefficientIntegral_linear_eval μ c hf (c.coord i)).symm

/-- The coefficient integral in an algebraic finite-dimensional complex vector
space, computed in its canonical chosen finite basis. -/
def finiteDimensionalCoefficientIntegral [Module.Finite ℂ A] (f : X → A) : A :=
  basisCoefficientIntegral μ (Module.finBasis ℂ A) f

theorem finiteDimensionalCoefficientIntegral_linear_eval [Module.Finite ℂ A]
    {f : X → A} (hf : IsScalarIntegrable μ f) (L : A →ₗ[ℂ] ℂ) :
    L (finiteDimensionalCoefficientIntegral μ f) = ∫ x, L (f x) ∂μ :=
  basisCoefficientIntegral_linear_eval μ (Module.finBasis ℂ A) hf L

/-- Scalar integrability is preserved by any algebraic linear map. -/
theorem IsScalarIntegrable.linear_map {f : X → A} (hf : IsScalarIntegrable μ f)
    (L : A →ₗ[ℂ] B) : IsScalarIntegrable μ (fun x => L (f x)) := by
  intro T
  exact hf (T.comp L)

/-- The finite-dimensional coefficient integral is natural for algebraic linear
maps between finite-dimensional spaces. -/
theorem finiteDimensionalCoefficientIntegral_map [Module.Finite ℂ A] [Module.Finite ℂ B]
    {f : X → A} (hf : IsScalarIntegrable μ f) (L : A →ₗ[ℂ] B) :
    finiteDimensionalCoefficientIntegral μ (fun x => L (f x)) =
      L (finiteDimensionalCoefficientIntegral μ f) := by
  apply (Module.finBasis ℂ B).ext_elem
  intro i
  exact (finiteDimensionalCoefficientIntegral_linear_eval μ (IsScalarIntegrable.linear_map μ hf L)
    ((Module.finBasis ℂ B).coord i)).trans
    (finiteDimensionalCoefficientIntegral_linear_eval μ hf
      (((Module.finBasis ℂ B).coord i).comp L)).symm

/-- Regard a function as taking values in the algebraic span of its range. -/
def coefficientSpanFunction (f : X → A) (x : X) : Submodule.span ℂ (Set.range f) :=
  ⟨f x, Submodule.subset_span (Set.mem_range_self x)⟩

/-- The integral of a function whose value span is finite-dimensional. -/
def finiteSpanCoefficientIntegral (f : X → A)
    [Module.Finite ℂ (Submodule.span ℂ (Set.range f))] : A :=
  (finiteDimensionalCoefficientIntegral μ (coefficientSpanFunction f)).val

theorem finiteSpanCoefficientIntegral_linear_eval (f : X → A)
    [Module.Finite ℂ (Submodule.span ℂ (Set.range f))]
    (hf : IsScalarIntegrable μ (coefficientSpanFunction f)) (L : A →ₗ[ℂ] ℂ) :
    L (finiteSpanCoefficientIntegral μ f) = ∫ x, L (f x) ∂μ := by
  exact finiteDimensionalCoefficientIntegral_linear_eval μ hf
    (L.comp (Submodule.span ℂ (Set.range f)).subtype)

/-- Any linear constraint satisfied by all values is satisfied by their
coefficient integral. -/
theorem finiteSpanCoefficientIntegral_mem (f : X → A)
    [Module.Finite ℂ (Submodule.span ℂ (Set.range f))]
    (S : Submodule ℂ A) (hf : ∀ x, f x ∈ S) :
    finiteSpanCoefficientIntegral μ f ∈ S := by
  have hle : Submodule.span ℂ (Set.range f) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hf x
  exact hle (finiteDimensionalCoefficientIntegral μ (coefficientSpanFunction f)).property

end Langlands.Conductor
