import Langlands.Representation.Archimedean.RealPrincipalSeriesFrobeniusRealization
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages

/-! # Recovery of the compact-finite Frobenius image by compact averaging -/

noncomputable section

open Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open OrthogonalFinitePolynomial RealPrincipalSeriesDuality

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] OrthogonalFinitePolynomial.secondCountableTopology_orthogonal
attribute [local instance] measurableSpaceK borelSpaceK

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "I" => matrixModel ℝ n
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {e : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)

local notation "W" => (frobeniusClosure hgk hℓ : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ
local notation "j" => frobeniusClosureMap hgk hℓ

private theorem continuous_orthogonalOrbit (x : Hilbert a e) :
    Continuous (fun k : O => representation a e (Unitary.toUnits k) x) := by
  have hu : Continuous (Unitary.toUnits : O → GL) :=
    continuous_subtype_val.comp (continuous_orthogonalCompactEquiv (n := n))
  have hi : Continuous (fun k : O => (Unitary.toUnits k, x)) := hu.prodMk continuous_const
  have h := (isContinuousRepresentation a e).comp hi
  simpa only [Function.comp_def] using h

theorem orthogonalAverage_mem (φ : C(O, ℂ)) {P : Submodule ℂ (Hilbert a e)}
    (hP : IsClosed (P : Set (Hilbert a e))) {x : Hilbert a e}
    (hx : ∀ k : O, representation a e (Unitary.toUnits k) x ∈ P) :
    orthogonalAverage a e φ x ∈ P := by
  rw [orthogonalAverage_apply]
  have hC : Continuous (fun k : O => φ k • representation a e (Unitary.toUnits k) x) :=
    φ.continuous.smul (continuous_orthogonalOrbit (a := a) (e := e) x)
  have hI := OrthogonalFinitePolynomial.integrable_of_continuous (haarOrthogonal n) hC
  exact (P.restrictScalars ℝ).convex.integral_mem hP
    (Eventually.of_forall fun k => P.smul_mem (φ k) (hx k)) hI

private theorem orthogonalAverage_mem_range_of_image (φ : C(O, ℂ)) (v : V) :
    orthogonalAverage a e φ (frobeniusHilbert hgk hℓ v) ∈ LinearMap.range (frobeniusHilbert hgk hℓ) := by
  let B := frobeniusHilbert hgk hℓ
  let P := (FiniteVectors.orbitSpan ρ v).map B
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v) := hgk.1 v
  have hP : FiniteDimensional ℂ P := inferInstance
  have hmem : orthogonalAverage a e φ (B v) ∈ P := by
    apply orthogonalAverage_mem φ P.closed_of_finiteDimensional
    intro k
    change representation a e ((orthogonalCompactEquiv n k : unitaryCompact ℝ n) : GL) (B v) ∈ P
    rw [representation_frobeniusHilbert_compact hgk hℓ]
    exact ⟨ρ k v, FiniteVectors.action_mem_orbitSpan ρ k v, rfl⟩
  obtain ⟨w, -, hw⟩ := hmem
  exact ⟨w, hw⟩

/-- Every polynomial-weighted average of a vector in the Frobenius closure belongs to the
algebraic Frobenius image. -/
theorem orthogonalAverage_mem_frobeniusRange {φ : C(O, ℂ)} (hφ : φ ∈ polynomialStar n)
    {x : Hilbert a e} (hx : x ∈ frobeniusClosure hgk hℓ) :
    orthogonalAverage a e φ x ∈ LinearMap.range (frobeniusHilbert hgk hℓ) := by
  let B := frobeniusHilbert hgk hℓ
  let T := orthogonalAverage a e φ
  let P := LinearMap.range B ⊓ LinearMap.range T.toLinearMap
  have hR : FiniteDimensional ℂ (LinearMap.range T.toLinearMap) :=
    finiteDimensional_orthogonalAverage_range a e hφ
  have hP : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le inf_le_right
  have hclosed : IsClosed (T ⁻¹' (P : Set (Hilbert a e))) := P.closed_of_finiteDimensional.preimage T.continuous
  have hle : Set.range B ⊆ T ⁻¹' (P : Set (Hilbert a e)) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨orthogonalAverage_mem_range_of_image hgk hℓ φ v, ⟨B v, rfl⟩⟩
  exact (show T x ∈ P from closure_minimal hle hclosed hx).1

/-- A vector in the Hilbert closure with finite-dimensional compact orbit span comes from
an algebraic Frobenius vector. -/
theorem mem_frobenius_range_of_finite_orbit (x : Hilbert a e) (hx : x ∈ frobeniusClosure hgk hℓ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : O =>
      representation a e (Unitary.toUnits k) x))) : x ∈ LinearMap.range (frobeniusHilbert hgk hℓ) := by
  let U := Submodule.span ℂ (Set.range fun k : O => representation a e (Unitary.toUnits k) x)
  let P := LinearMap.range (frobeniusHilbert hgk hℓ) ⊓ U
  have hP : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le inf_le_right
  let f : C(O, Hilbert a e) := ⟨fun k => representation a e (Unitary.toUnits k) x,
    continuous_orthogonalOrbit (a := a) (e := e) x⟩
  have havg (φ : C(O, ℂ)) (hφ : φ ∈ polynomialStar n) :
      (∫ k, φ k • f k ∂haarOrthogonal n) ∈ P := by
    change orthogonalAverage a e φ x ∈ P
    refine ⟨orthogonalAverage_mem_frobeniusRange hgk hℓ hφ hx, ?_⟩
    exact orthogonalAverage_mem φ U.closed_of_finiteDimensional
      (fun k => Submodule.subset_span ⟨k, rfl⟩)
  have he := mem_closedSubmodule_of_polynomial_integrals_mem (E := Hilbert a e)
    (haarOrthogonal n) f P.closed_of_finiteDimensional havg 1
  have h1 : f 1 = x := by
    change representation a e (Unitary.toUnits (1 : O)) x = x
    simp
  rw [h1] at he
  exact he.1

private def restrictToSubmodule {D : Type*} [AddCommGroup D] [Module ℂ D]
    {B : V →ₗ[ℂ] D} {P : Submodule ℂ D} (hB : ∀ v, B v ∈ P) :=
  B.codRestrict P hB

set_option backward.isDefEq.respectTransparency true in
/-- The Frobenius map into the compact-finite subspace of the genuine smooth carrier. -/
def frobeniusKFiniteMap :=
  restrictToSubmodule (B := frobeniusSmoothMap hgk hℓ)
    (frobeniusSmoothMap_mem_kFinite hgk hℓ)

private def forgetSmooth {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : GL →* (H →L[ℂ] H)) : DerivativeSmoothVectors I A →ₗ[ℂ] H :=
  (smoothVectors I A).subtype.comp (DerivativeSmoothVectors.toSmooth I A).toLinearMap

set_option maxHeartbeats 800000 in
theorem surjective_frobeniusKFiniteMap : Function.Surjective (frobeniusKFiniteMap hgk hℓ) := by
  intro y
  let p₀ := forgetSmooth (n := n) (H := W) R
  let p := (frobeniusClosure hgk hℓ).subtype.comp p₀
  let s := smoothHilbertCompactRepresentation ℝ n (H := W) R
  let U := FiniteVectors.orbitSpan s y.1
  have hU : FiniteDimensional ℂ U := y.2
  have hle : Submodule.span ℂ (Set.range fun k : O =>
      representation a e (Unitary.toUnits k) (p y.1)) ≤ U.map p := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨s k y.1, FiniteVectors.action_mem_orbitSpan s k y.1, rfl⟩
  have hX : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : O =>
      representation a e (Unitary.toUnits k) (p y.1))) :=
    Submodule.finiteDimensional_of_le hle
  obtain ⟨v, hv⟩ := mem_frobenius_range_of_finite_orbit hgk hℓ (p y.1) (p₀ y.1).2 hX
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply (DerivativeSmoothVectors.toSmooth I (E := W) R).injective
  apply Subtype.ext
  apply Subtype.ext
  exact hv

set_option backward.isDefEq.respectTransparency true in
/-- For an irreducible module and a nonzero Jacquet functional, Frobenius identifies the
algebraic module with all compact-finite vectors in the genuine smooth carrier. -/
def frobeniusKFiniteEquiv (hirr : IsIrreducibleGKModule ρ π) (h₀ : ℓ ≠ 0) :=
  LinearEquiv.ofBijective (frobeniusKFiniteMap hgk hℓ)
    ⟨fun _ _ h => frobeniusSmoothMap_injective hgk hℓ hirr h₀ (congrArg Subtype.val h),
      surjective_frobeniusKFiniteMap hgk hℓ⟩

end Langlands.Archimedean.RealPrincipalSeriesHilbert
