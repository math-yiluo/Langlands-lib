import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.DistinguishedCompletionGlobalization
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.TraceFormula.CyclicFieldGlobalizationProof

/-! # Cyclic globalization with a distinguished completion and two split places -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality TraceFormula
open scoped FiniteExtension

universe u v

/-- A characteristic-zero cyclic local field extension has a compatible
number-field globalization with a unique upper place at the distinguished
completion, two other split finite places and all infinite places split. -/
def CyclicGlobalizationWithSplitPlacesStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∃ (K L : Type) (_ : Field K) (_ : NumberField K) (_ : Field L) (_ : NumberField L)
      (_ : Algebra K L) (_ : IsGalois K L) (_ : IsCyclic (L ≃ₐ[K] L))
      (_ : CompactSpace (AdeleQuotient K)) (_ : CompactSpace (AdeleQuotient L))
      (σ₀ : L ≃ₐ[K] L),
      IsCyclicAlgebra σ₀ l ∧
      (∀ z : NumberField.InfinitePlace K, IsCyclicShiftSplit K L z.Completion σ₀ l) ∧
    ∃ (p : FinitePlace K) (w : FinitePlacesAbove L p)
      (hw : ∀ z : FinitePlacesAbove L p, z = w)
      (a : F ≃+* p.adicCompletion K) (b : E ≃+* w.1.adicCompletion L),
      Continuous a ∧ Continuous a.symm ∧ Continuous b ∧ Continuous b.symm ∧
      (∀ x : F, b (algebraMap F E x) = algebraMap (p.adicCompletion K) (w.1.adicCompletion L) (a x)) ∧
      (∀ x : E, b (σ x) = uniquePlaceCompletionAutEquiv w hw σ₀ (b x)) ∧
    ∃ v₁ v₂ : FinitePlace K, v₁ ≠ p ∧ v₂ ≠ p ∧ v₁ ≠ v₂ ∧
      IsCyclicShiftSplit K L (v₁.adicCompletion K) σ₀ l ∧
      IsCyclicShiftSplit K L (v₂.adicCompletion K) σ₀ l

set_option maxHeartbeats 3000000 in
theorem cyclicGlobalizationWithSplitPlaces : CyclicGlobalizationWithSplitPlacesStatement.{u, v} := by
  classical
  intro F fF _ tF _ _ E fE _ tE _ aFE _ σ l hcyc
  obtain ⟨K, L, fK, fL, nK, nL, aKL, σ₀, hcyc₀, hinfinite, ⟨p, a, b, ha, ha', hab, hσ, hb⟩, hsplit, -⟩ :=
    cyclicFieldGlobalization F E σ l hcyc (Field.toIsField E)
  let : FiniteDimensional K L := hcyc₀.1
  let gKL : IsGalois K L := hcyc₀.isGalois
  have hord : orderOf σ₀ = Nat.card (L ≃ₐ[K] L) := by
    rw [IsGalois.card_aut_eq_finrank, hcyc₀.2.1, hcyc₀.2.2.2.1]
  let cKL : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_orderOf_eq_card σ₀ hord
  obtain ⟨w, hw, -, e, he, he', hs, ht⟩ :=
    @distinguishedCompletionGlobalization.{u, v} K L fK fL nK nL aKL gKL p σ₀
      F E fF fE aFE tF tE σ a b ha ha' hab hσ hb
  obtain ⟨v₁, hv₁, -, hs₁⟩ := hsplit {p} 0
  obtain ⟨v₂, hv₂, -, hs₂⟩ := hsplit {p, v₁} 0
  have h₁ : v₁ ≠ p := by simpa only [Finset.mem_singleton] using hv₁
  have h₂ : v₂ ≠ p := fun h => hv₂ (by simp [h])
  have h₁₂ : v₁ ≠ v₂ := fun h => hv₂ (by simp [← h])
  exact ⟨K, L, fK, nK, fL, nL, aKL, gKL, cKL, compactSpace_adeleQuotient K, compactSpace_adeleQuotient L,
    σ₀, hcyc₀, hinfinite, p, w, hw, a.symm, e, ha', ha, he, he', hs, ht, v₁, v₂, h₁, h₂, h₁₂, hs₁, hs₂⟩

end Langlands.BaseChange
