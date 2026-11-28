import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Langlands.Global.AdelicFunctoriality.UniquePlaceCompletion
import Langlands.Global.AdeleQuotientStatement

/-! # Totally complex cyclic globalization with two split finite places -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality TraceFormula
open scoped FiniteExtension

universe u v

/-- A cyclic extension of characteristic-zero local fields has a globalization
over a totally complex number field with the actual distinguished completions
and two other split finite places. -/
def CyclicGlobalizationWithSplitPlacesTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∃ (K L : Type) (_ : Field K) (_ : NumberField K) (_ : Field L) (_ : NumberField L)
      (_ : Algebra K L) (_ : IsGalois K L) (_ : IsCyclic (L ≃ₐ[K] L))
      (_ : CompactSpace (AdeleQuotient K)) (_ : CompactSpace (AdeleQuotient L))
      (_ : NumberField.IsTotallyComplex K) (σ₀ : L ≃ₐ[K] L),
      IsCyclicAlgebra σ₀ l ∧
      (∀ z : NumberField.InfinitePlace K, IsCyclicShiftSplit K L z.Completion σ₀ l) ∧
    ∃ (p : FinitePlace K) (w : FinitePlacesAbove L p)
      (hw : ∀ z : FinitePlacesAbove L p, z = w)
      (a : F ≃+* p.adicCompletion K) (b : E ≃+* w.1.adicCompletion L),
      Continuous a ∧ Continuous a.symm ∧ Continuous b ∧ Continuous b.symm ∧
      (∀ x : F, b (algebraMap F E x) =
        algebraMap (p.adicCompletion K) (w.1.adicCompletion L) (a x)) ∧
      (∀ x : E, b (σ x) = uniquePlaceCompletionAutEquiv w hw σ₀ (b x)) ∧
    ∃ v₁ v₂ : FinitePlace K, v₁ ≠ p ∧ v₂ ≠ p ∧ v₁ ≠ v₂ ∧
      IsCyclicShiftSplit K L (v₁.adicCompletion K) σ₀ l ∧
      IsCyclicShiftSplit K L (v₂.adicCompletion K) σ₀ l

end Langlands.BaseChange
