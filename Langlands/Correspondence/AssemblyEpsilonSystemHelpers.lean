import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.Weil.Representation.CharacterLine

noncomputable section

universe uG uV uF uP uA

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- A scalar character line has no nontrivial proper subrepresentation. -/
theorem characterLine_isIrreducible (χ : G →* ℂˣ) :
    (characterLine.{uG, uV} χ).IsIrreducible := by
  change Representation.IsIrreducible
    (Langlands.twist χ (Representation.trivial ℂ G (ULift.{uV} ℂ)))
  let : IsSimpleModule ℂ (ULift.{uV} ℂ) :=
    IsSimpleModule.congr (ULift.moduleEquiv : ULift.{uV} ℂ ≃ₗ[ℂ] ℂ)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro S
    exact (eq_bot_or_eq_top S.toSubmodule).imp
      (fun h => Subrepresentation.toSubmodule_injective h)
      (fun h => Subrepresentation.toSubmodule_injective h)

variable [TopologicalSpace G]

/-- The genuine rank-one continuous irreducible class of a continuous character. -/
def continuousIrreducibleCharacterClass (χ : G →ₜ* ℂˣ) :
    ContinuousIrreducibleClasses.{uG, uV} G 1 :=
  ⟨Quotient.mk _ ⟨characterLine χ.toMonoidHom,
      characterLine_isContinuous χ, characterLine_isIrreducible χ.toMonoidHom⟩,
    characterLine_rank χ.toMonoidHom⟩

end Langlands.FiniteRepresentation

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A rank-one test class exists in every parameter carrier universe. -/
theorem nonempty_irreducibleWeilClass_one :
    Nonempty (IrreducibleWeilClass.{uF, uP} F 1) :=
  ⟨FiniteRepresentation.continuousIrreducibleCharacterClass
    (1 : Weil.Local.localWeilGroup F →ₜ* ℂˣ)⟩

/-- Supercuspidal factor compatibility already contains self-dual measure existence. -/
theorem SupercuspidalPairFactorCompatibility.exists_selfDualMeasure
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uP} F}
    {hε : NonabelianSystem.IsSystem F eC ε} {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (h : SupercuspidalPairFactorCompatibility F eC ε hε c0)
    (ψ : NontrivialAdditiveCharacter F) :
    ∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν := by
  obtain ⟨σ⟩ := nonempty_irreducibleWeilClass_one.{uF, uP} F
  exact (h ψ 0 0 σ σ).1

/-- The correspondence premise supplies self-dual measures at every character. -/
theorem IsSupercuspidalCorrespondence.exists_selfDualMeasure
    {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (h : IsSupercuspidalCorrespondence F c0) (ψ : NontrivialAdditiveCharacter F) :
    ∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν := by
  obtain ⟨_, _, e, _, _, _, _, eC, ε, hε, _, hcompat⟩ := h
  exact hcompat.exists_selfDualMeasure F ψ

end Langlands.Correspondence
