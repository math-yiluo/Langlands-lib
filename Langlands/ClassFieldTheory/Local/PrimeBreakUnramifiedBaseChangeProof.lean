import Langlands.ClassFieldTheory.Local.PrimeBreakUnramifiedBaseChangeStatement
import Langlands.ClassFieldTheory.Local.PrimeBreakUnramifiedBaseChangeSupport
import Langlands.LocalFactor.Ramification.UniformizerCriterionProof

/-! Preservation of the prime break by the actual restriction and uniformizer test. -/

noncomputable section

namespace Langlands.LocalClassField

open IntermediateField

universe u

/-- The actual prime single-break pattern is preserved by every finite unramified
base change and every presentation of the compositum. -/
theorem primeBreakUnramifiedBaseChange : PrimeBreakUnramifiedBaseChange.{u} := by
  classical
  intro p _ F E K' _ ell _hell htot hunr M hM hE hK
  let := (E.asPadicField (p := p)).algebra
  let := (K'.asPadicField (p := p)).algebra
  let := (M.asPadicField (p := p)).algebra
  let : Algebra E.field M.field := (inclusion hE).toAlgebra
  let : Algebra K'.field M.field := (inclusion hK).toAlgebra
  let : IsScalarTower (Padic p) F.Carrier E.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) E.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) K'.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro t hbreak i
  let TE := (E.asPadicField (p := p)).canonicalTopologicalData
  let TK := (K'.asPadicField (p := p)).canonicalTopologicalData
  let TM := (M.asPadicField (p := p)).canonicalTopologicalData
  obtain ⟨hsurjM, hord⟩ := primeBreakCompositumData F E K' M htot hunr hM hE hK
  have hsurjE := primeBreakResidueMap_surjective_of_total F (E.asPadicField (p := p)) htot
  have hπM : TM.ord (inclusion hE TE.uniformizer) = 1 :=
    (hord TE.uniformizer).trans TE.ord_uniformizer
  have hmem (σ : M.field ≃ₐ[K'.field] M.field) :
      σ ∈ Ramification.Padic.lowerRamificationGroup TM K'.field i ↔
        primeBreakRestriction E.field K'.field M.field hE hK σ ∈
          Ramification.Padic.lowerRamificationGroup TE F.Carrier i := by
    rw [Ramification.Padic.mem_lowerRamificationGroup_iff_uniformizer
      TK TM hsurjM (inclusion hE TE.uniformizer) hπM,
      Ramification.Padic.mem_lowerRamificationGroup_iff_uniformizer
        F.canonicalTopologicalData TE hsurjE TE.uniformizer TE.ord_uniformizer]
    exact primeBreakRestriction_displacement E.field K'.field M.field hE hK
      TE.ord TM.ord hord σ TE.uniformizer (i + 1 : ℤ)
  by_cases hi : i ≤ t
  · rw [ite_eq_left hi]
    apply top_unique
    intro σ _
    apply (hmem σ).mpr
    rw [hbreak i, ite_eq_left hi]
    exact Subgroup.mem_top _
  · rw [ite_eq_right hi]
    apply bot_unique
    intro σ hσ
    have hrσ : primeBreakRestriction E.field K'.field M.field hE hK σ = 1 := by
      have h := (hmem σ).mp hσ
      rw [hbreak i, ite_eq_right hi] at h
      exact Subgroup.mem_bot.mp h
    apply Subgroup.mem_bot.mpr
    apply primeBreakRestriction_injective E.field K'.field M.field hE hK hM
    exact hrσ.trans (map_one _).symm

end Langlands.LocalClassField
