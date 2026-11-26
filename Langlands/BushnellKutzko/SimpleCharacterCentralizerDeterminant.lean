import Langlands.BushnellKutzko.SimpleCharacters
import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.SubfieldLatticeChain

/-! # Determinant factorization on the centralizer of a simple stratum -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- The algebraic extension of the determinant implication in BK93 (2.4.11), on a
simple character domain. Its input is an abstract group homomorphism. -/
def SimpleCharacterCentralizerDeterminantStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice), S.IsSimple → ∀ m : ℕ,
      ∀ η : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ,
        (centralizerUnitGroup S.b : Set (Module.End F V)ˣ) ⊆ characterSelfIntertwining η →
          factorsThroughCentralizerDet S.b η

set_option maxHeartbeats 1600000 in
/-- Specialize the algebraic filtered-unit determinant assertion to the generated field. -/
theorem simpleCharacterCentralizerDeterminant_of_unitFiltration
    (hdet : ∀ (E : Type uV) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] (V : Type uV) [AddCommGroup V] [Module E V]
      (M : LatticeChain 𝒪[E] E V) (m : ℕ) (χ : M.unitFiltration (m + 1) →* ℂˣ),
      characterSelfIntertwining χ = Set.univ →
      let d := (Units.map (LinearMap.det : Module.End E V →* E)).comp
        (M.unitFiltration (m + 1)).subtype
      ∃ ξ : d.range →* ℂˣ, ∀ x : M.unitFiltration (m + 1), χ x = ξ (d.rangeRestrict x)) :
    SimpleCharacterCentralizerDeterminantStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ S q hS m η hIntertwining
  let L := S.chain
  let H := simpleHGroup L S.n S.b q.tail (m + 1)
  obtain ⟨hE, hnormalize⟩ := hS.1.1
  let E := elementAlgebra S.b
  let : Field E := hE.toField
  let := L.finiteDimensional
  let := L.finiteDimensional_subfield E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let M := L.relativeLatticeChain hnormalize (isIntegral_iff_mem_spectralInteger F E)
  let i := relativeEndUnits (F := F) (V := V) E
  have hcentralizer (x : (Module.End E V)ˣ) : i x ∈ centralizerUnitGroup S.b := by
    change Commute S.b ((x : Module.End E V).restrictScalars F)
    rw [← subfieldEmbedding_elementGenerator S.b hE]
    ext v
    exact ((x : Module.End E V).map_smul (elementGenerator S.b) v).symm
  have hU : H.comap i = M.unitFiltration (m + 1) := by
    ext x
    change i x ∈ H ↔ x ∈ M.unitFiltration (m + 1)
    have hunit : x ∈ M.unitFiltration (m + 1) ↔ i x ∈ L.unitFiltration (m + 1) := Iff.rfl
    rw [hunit]
    refine ⟨fun h => simpleHGroup_le_unitFiltration L S.n S.b q.tail (m + 1) h, fun hx => ?_⟩
    have hc : (i x : Module.End F V) ∈ centralizerLattice L S.b 0 := by
      refine ⟨hx.1, ?_⟩
      change S.b * (i x : Module.End F V) - (i x : Module.End F V) * S.b = 0
      exact sub_eq_zero.mpr (hcentralizer x)
    apply Subgroup.subset_closure
    refine ⟨hx, ?_⟩
    generalize q.tail = tail
    cases tail <;> exact Submodule.mem_sup_left hc
  let U := H.comap i
  let ι : U →* H := (i.comp U.subtype).codRestrict H (fun x => x.property)
  let χ := η.comp ι
  have hχ : characterSelfIntertwining χ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g x hx
    have hcov : i g * (ι x : (Module.End F V)ˣ) * (i g)⁻¹ ∈ H := by
      change i (g * (x : (Module.End E V)ˣ) * g⁻¹) ∈ H at hx
      change i g * i (x : (Module.End E V)ˣ) * (i g)⁻¹ ∈ H
      simpa only [map_mul, map_inv] using hx
    exact hIntertwining (hcentralizer g) (ι x) hcov
  have hfactor (K : Subgroup (Module.End E V)ˣ) (hk : K = M.unitFiltration (m + 1)) :
      ∀ χ : K →* ℂˣ, characterSelfIntertwining χ = Set.univ →
        let d := (Units.map (LinearMap.det : Module.End E V →* E)).comp K.subtype
        ∃ ξ : d.range →* ℂˣ, ∀ x : K, χ x = ξ (d.rangeRestrict x) := by
    subst K
    exact hdet E V M m
  exact ⟨hE, hfactor U hU χ hχ⟩

end Langlands.BushnellKutzko
