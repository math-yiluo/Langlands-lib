import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Corrected abelian full-subcategory criteria and a dimension-one counterexample

Statement targets correcting Renard 2026, Appendix A.VI.1, printed page 261
(PDF page 267). The original subobject/quotient closure claim omits a
finite-product hypothesis. These declarations state sufficient corrections and
an explicit counterexample; they do not prove these results.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CategoryTheory

/-- Zero containment and closure under kernels, cokernels and finite products
suffice for a full subcategory of an abelian category to admit an abelian structure. -/
def AbelianOfKernelsCokernelsFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] (P : ObjectProperty C) : Prop :=
  P.ContainsZero →
    P.IsClosedUnderKernels →
    P.IsClosedUnderCokernels →
    P.IsClosedUnderFiniteProducts →
    Nonempty (Abelian P.FullSubcategory)

/-- A strengthened correction of Renard's sufficient criterion: add zero
containment and finite-product closure to subobject and quotient closure. -/
def AbelianOfSubobjectsQuotientsFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] (P : ObjectProperty C) : Prop :=
  P.ContainsZero →
    P.IsClosedUnderSubobjects →
    P.IsClosedUnderQuotients →
    P.IsClosedUnderFiniteProducts →
    Nonempty (Abelian P.FullSubcategory)

/-- The actual property of vector spaces of dimension zero or one.
Finite-dimensionality is essential alongside the natural-number finrank bound. -/
def dimensionLEOneProperty (K : Type u) [Field K] :
    ObjectProperty (ModuleCat.{u} K) :=
  fun V => FiniteDimensional K V ∧ Module.finrank K V ≤ 1

/-- The full subcategory of vector spaces of dimension zero or one, with
module carriers in the same universe as the field. -/
abbrev DimensionLEOneModuleCat (K : Type u) [Field K] :=
  (dimensionLEOneProperty K).FullSubcategory

/-- The actual one-dimensional vector space `K`, as an object of the
dimension-at-most-one full subcategory. Only its intrinsic membership is proved. -/
abbrev dimensionLEOneLine (K : Type u) [Field K] : DimensionLEOneModuleCat K :=
  ⟨ModuleCat.of K K, ⟨inferInstance, by simp⟩⟩

/-- The dimension-at-most-one property contains a zero object and is closed
under every ambient subobject and every ambient quotient. -/
def DimensionLEOneClosedUnderSubobjectsQuotients (K : Type u) [Field K] : Prop :=
  (dimensionLEOneProperty K).ContainsZero ∧
    (dimensionLEOneProperty K).IsClosedUnderSubobjects ∧
    (dimensionLEOneProperty K).IsClosedUnderQuotients

/-- No object with any pair of projection maps in the full subcategory is a
categorical binary product of the line with itself. -/
def DimensionLEOneLineHasNoBinaryProduct (K : Type u) [Field K] : Prop :=
  ¬ HasBinaryProduct (dimensionLEOneLine K) (dimensionLEOneLine K)

/-- The dimension-at-most-one full subcategory admits no abelian structure. -/
def DimensionLEOneNotAbelian (K : Type u) [Field K] : Prop :=
  ¬ Nonempty (Abelian (DimensionLEOneModuleCat K))

end Langlands.CategoryTheory
