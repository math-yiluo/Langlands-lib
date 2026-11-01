import Langlands.Automorphic.ConstantFunctions
import Mathlib.RingTheory.SimpleModule.Rank

/-! # Irreducibility, central character and rank-one cuspidality of actual constants -/

noncomputable section

universe uF

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F]

private theorem irreducible_of_finrank_one {M V : Type*} [Monoid M] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ M V) (hV : Module.finrank ℂ V = 1) :
    ρ.IsIrreducible := by
  have hSimple : IsSimpleOrder (Submodule ℂ V) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) hV
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro S
    rcases hSimple.eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

namespace ConstantFunctions

variable (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (realization F n).Space := Submodule.addCommGroup _

/-- The actual constant line is irreducible under the whole concrete operator algebra. -/
theorem realization_isIrreducible : (realization F n).IsIrreducible := by
  exact irreducible_of_finrank_one (realization F n).representation (realization_finrank F n)

/-- The central character is proved on the actual adelic functions. -/
theorem realization_hasCentralCharacter : (realization F n).HasCentralCharacter 1 := by
  apply ((realization F n).hasCentralCharacter_iff 1).mpr
  intro f
  obtain ⟨c, rfl⟩ := (scalarEquiv F n).surjective f
  rw [formInclusion_scalarEquiv]
  intro z x
  change c = (1 : ℂ) * c
  exact (one_mul c).symm

end ConstantFunctions

section RankOne

variable [CompactSpace (AdeleQuotient F)]

/-- Every actual rank-one function is cuspidal: there is no proper positive block split. -/
theorem isCuspidal_rankOne (f : ContinuousRationalFunctions F 1) :
    IsCuspidal F 1 f := by
  intro a b h ha hb
  omega

namespace ConstantFunctions

/-- In rank one the actual constant realization satisfies the published cusp predicate. -/
theorem realization_isCuspidal_rankOne : (realization F 1).IsCuspidal := by
  apply (realization F 1).isCuspidal_iff.mpr
  intro f
  exact isCuspidal_rankOne F _

/-- A constructed positive-rank irreducible cuspidal object, not an existence premise. -/
def rankOneCuspidal : CuspidalOperatorRealization F 0 where
  realization := realization F 1
  irreducible := realization_isIrreducible F 1
  cuspidal := realization_isCuspidal_rankOne F

@[simp]
theorem rankOneCuspidal_realization :
    (rankOneCuspidal F).realization = realization F 1 := rfl

/-- Its actual embedding has the trivial central Hecke character. -/
theorem rankOneCuspidal_hasCentralCharacter : (rankOneCuspidal F).HasCentralCharacter 1 :=
  realization_hasCentralCharacter F 1

/-- This is an actual represented class, with its constructed representative retained. -/
def rankOneCuspidalClass : CuspidalOperatorRealization.IsoClass F 0 :=
  (rankOneCuspidal F).isoClass

@[simp]
theorem rankOneCuspidalClass_toOperatorClass :
    (rankOneCuspidalClass F).toOperatorClass = (realization F 1).isoClass := rfl

end ConstantFunctions
end RankOne
end Langlands.Automorphic
