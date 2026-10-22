import Langlands.HarmonicAnalysis.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-! The plus-sign Fourier integral on the actual finite row space. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe u

section ProductMeasure

variable {F : Type u} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

/-- The finite product of the supplied scalar Haar measure. -/
def rowMeasure (μ : AdditiveHaarMeasure F) (d : ℕ) : Measure (Fin d → F) :=
  Measure.pi (fun _ : Fin d => μ.measure)

instance rowMeasure_sigmaFinite (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] (d : ℕ) : SigmaFinite (rowMeasure μ d) :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun _ : Fin d => μ.measure)))

instance rowMeasure_isAddHaar [MeasurableAdd₂ F] (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] (d : ℕ) : (rowMeasure μ d).IsAddHaarMeasure :=
  inferInstanceAs (Measure.pi (fun _ : Fin d => μ.measure)).IsAddHaarMeasure

instance rowMeasure_isFiniteOnCompacts (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] (d : ℕ) :
    IsFiniteMeasureOnCompacts (rowMeasure μ d) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi (fun _ : Fin d => μ.measure)))

@[simp] theorem rowMeasure_zero (μ : AdditiveHaarMeasure F) :
    rowMeasure μ 0 = Measure.dirac 0 :=
  Measure.pi_of_empty _ _

/-- The product normalization is explicit, including dimension zero. -/
theorem rowMeasure_entries (μ : AdditiveHaarMeasure F) [SigmaFinite μ.measure]
    (d : ℕ) (S : Set F) :
    rowMeasure μ d {x | ∀ i, x i ∈ S} = μ.measure S ^ d := by
  have he : {x : Fin d → F | ∀ i, x i ∈ S} =
      Set.univ.pi (fun _ : Fin d => S) := by
    ext x
    simp
  rw [he]
  simp [rowMeasure, Measure.pi_pi]

end ProductMeasure

section Fourier

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] {d : ℕ}

/-- The bilinear row pairing, with no conjugation and no minus sign. -/
def rowPairing (x y : Fin d → F) : F := ∑ i, x i * y i

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_rowPairing_left (y : Fin d → F) :
    Continuous (fun x => rowPairing x y) := by
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

/-- Raw integral with the same scalar Haar measure in every coordinate.
The following theorem proves convergence on the actual test-function space. -/
def rowFourierIntegral (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (d : ℕ) (f : (Fin d → F) → ℂ) (y : Fin d → F) : ℂ :=
  ∫ x, ψ.complex (rowPairing x y) * f x ∂rowMeasure μ d

variable [BorelSpace (Fin d → F)]

omit [BorelSpace F] in
theorem rowFourierIntegrand_integrable (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) [SigmaFinite μ.measure]
    (f : SchwartzBruhat (Fin d → F)) (y : Fin d → F) :
    Integrable (fun x => ψ.complex (rowPairing x y) * f x) (rowMeasure μ d) := by
  have hc := (ψ.continuous_complex.comp (continuous_rowPairing_left y)).mul f.continuous
  exact hc.integrable_of_hasCompactSupport f.hasCompactSupport.mul_left

/-- Complex-linear Fourier transform into all functions. Its image is not
asserted to lie in the Schwartz--Bruhat subspace by this construction. -/
def rowFourierTransform (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] :
    SchwartzBruhat (Fin d → F) →ₗ[ℂ] ((Fin d → F) → ℂ) where
  toFun f := rowFourierIntegral ψ μ d f
  map_add' f g := by
    ext y
    change (∫ x, ψ.complex (rowPairing x y) * (f x + g x) ∂rowMeasure μ d) =
      (∫ x, ψ.complex (rowPairing x y) * f x ∂rowMeasure μ d) +
      ∫ x, ψ.complex (rowPairing x y) * g x ∂rowMeasure μ d
    simp_rw [mul_add]
    exact integral_add (rowFourierIntegrand_integrable ψ μ f y)
      (rowFourierIntegrand_integrable ψ μ g y)
  map_smul' c f := by
    ext y
    change (∫ x, ψ.complex (rowPairing x y) * (c * f x) ∂rowMeasure μ d) =
      c * ∫ x, ψ.complex (rowPairing x y) * f x ∂rowMeasure μ d
    simp_rw [mul_left_comm (ψ.complex _) c]
    exact integral_const_mul c _

/-- Two actual test functions are a Fourier pair precisely when the second
equals the plus-sign integral of the first at every row vector. -/
def IsRowFourierPair (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (f g : SchwartzBruhat (Fin d → F)) : Prop :=
  ∀ y, g y = rowFourierIntegral ψ μ d f y

omit [IsTopologicalRing F] [BorelSpace F] [BorelSpace (Fin d → F)] in
theorem IsRowFourierPair.unique {ψ : UnitaryAdditiveCharacter F}
    {μ : AdditiveHaarMeasure F} {f g h : SchwartzBruhat (Fin d → F)}
    (hg : IsRowFourierPair ψ μ f g) (hh : IsRowFourierPair ψ μ f h) : g = h := by
  apply Subtype.ext
  funext y
  exact (hg y).trans (hh y).symm

/-- Preservation of the test space is an explicit theorem obligation. -/
def RowFourierClosed (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (d : ℕ) : Prop :=
  ∀ f : SchwartzBruhat (Fin d → F), ∃ g : SchwartzBruhat (Fin d → F),
    IsRowFourierPair ψ μ f g

/-- Intrinsic row-space self-duality, including convergence of the second
integral. No self-dual scalar measure is selected. -/
def IsRowSelfDual (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (d : ℕ) : Prop :=
  ∀ f : SchwartzBruhat (Fin d → F),
    (∀ y : Fin d → F, Integrable
      (fun x => ψ.complex (rowPairing x y) * rowFourierIntegral ψ μ d f x)
      (rowMeasure μ d)) ∧
    ∀ y : Fin d → F, rowFourierIntegral ψ μ d (rowFourierIntegral ψ μ d f) y = f (-y)

/-- Finite-dimensional Fourier preservation and inversion from the scalar
self-dual normalization. This proposition is not an available proof. -/
def RowFourierCompatibilityStatement [LocallyCompactSpace F] [T2Space F]
    [TotallyDisconnectedSpace F] (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (d : ℕ) : Prop :=
  IsSelfDual ψ μ → RowFourierClosed ψ μ d ∧ IsRowSelfDual ψ μ d

end Fourier

end Langlands.HarmonicAnalysis
