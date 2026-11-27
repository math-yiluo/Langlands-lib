import Langlands.BushnellKutzko.SimpleCharacterRestrictionLow
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement
import Langlands.BushnellKutzko.SimpleCharacterCentralizer
import Langlands.BushnellKutzko.CharacterNormalizerSubgroup

/-! # Normalizers of simple characters -/

noncomputable section

open ValuativeRel
open scoped Pointwise Classical

namespace Langlands.BushnellKutzko

universe uF uV

section Scalar

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "O" => 𝒪[F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerUnitGroup_eq_top_of_scalar {β : A} (hβ : elementAlgebra β = ⊥) :
    centralizerUnitGroup β = ⊤ := by
  have hb : β ∈ (⊥ : Subalgebra F A) := hβ ▸ Algebra.self_mem_adjoin_singleton F β
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hb
  exact (Subgroup.eq_top_iff' _).mpr fun g => Algebra.commutes c (g : A)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleHGroup_eq_unitFiltration_of_scalar (L : LatticeChain O F V)
    (n : ℤ) {β : A} (hβ : elementAlgebra β = ⊥) (m : ℕ) :
    simpleHGroup L n β [] m = L.unitFiltration m := by
  have hN : centralizerLattice L β 0 = L.endFiltration 0 := by
    apply inf_eq_left.mpr
    intro x hx
    rw [LinearMap.mem_ker]
    have hb : β ∈ (⊥ : Subalgebra F A) := hβ ▸ Algebra.self_mem_adjoin_singleton F β
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hb
    change β * x - x * β = 0
    rw [← hc, Algebra.commutes, sub_self]
  have hcarrier : simpleHCarrier L n β [] m = (L.unitFiltration m : Set G) := by
    ext g
    change (g ∈ L.unitFiltration m ∧
      (g : A) ∈ centralizerLattice L β 0 ⊔ L.endFiltration (simpleHCutoff n)) ↔
        g ∈ L.unitFiltration m
    rw [hN]
    exact ⟨And.left, fun hg => ⟨hg, Submodule.mem_sup_left hg.1⟩⟩
  rw [simpleHGroup, hcarrier, Subgroup.closure_eq]

/-- The scalar case of the simple-character intertwining and normalizer formulas. -/
theorem simpleCharacterIntertwining_of_scalar (ψF : AddChar F ℂ) (S : Stratum O F V)
    (q : S.DefiningSequenceChoice) (hβ : elementAlgebra S.b = ⊥) (m : ℕ)
    {θ : simpleHGroup S.chain S.n S.b q.tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m) :
    let Y := simpleCharacterIntertwiningFactor S q m
    let B := centralizerUnitGroup S.b
    let K := relativeOrderNormalizer S.chain S.b
    characterSelfIntertwining θ = Y * (B : Set G) * Y ∧
    characterNormalizer θ = Y * (K : Set G) := by
  dsimp only
  have hB := centralizerUnitGroup_eq_top_of_scalar hβ
  have hq := q.tail_eq_nil_of_scalar hβ
  have hdom : simpleHGroup S.chain S.n S.b q.tail (m + 1) = S.chain.unitFiltration (m + 1) := by
    rw [hq]
    exact simpleHGroup_eq_unitFiltration_of_scalar S.chain S.n hβ (m + 1)
  have hdet : factorsThroughCentralizerDet S.b θ := by
    generalize htail : q.tail = tail at θ hθ
    have ht : tail = [] := htail.symm.trans hq
    clear htail
    subst tail
    exact hθ.2
  have hI : characterSelfIntertwining θ = Set.univ := by
    refine Set.eq_univ_of_forall fun g h hh => hdet.conj_eq ?_ h ?_ hh
    · rw [hB]
      trivial
    · rw [hB]
      trivial
  have hY : simpleCharacterIntertwiningFactor S q m = (1 : Set G) := by
    rw [simpleCharacterIntertwiningFactor, ite_eq_left hβ]
    rfl
  have hK : relativeOrderNormalizer S.chain S.b = S.chain.stabilizer := by
    unfold relativeOrderNormalizer
    rw [hB, top_inf_eq]
  constructor
  · rw [hI, hY, hB]
    simp
  · rw [characterNormalizer, hI, Set.inter_univ, hY, one_mul, hK, hdom]
    rw [(normalizer F V S.chain).2.2.1 (m + 1)]

end Scalar

end Langlands.BushnellKutzko
