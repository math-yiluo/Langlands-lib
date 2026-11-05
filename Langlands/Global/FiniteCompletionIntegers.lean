import Langlands.Global.FiniteCompletionLocalField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Canonical integers of the original finite completion -/

noncomputable section

universe u

open scoped ValuativeRel WithZero

namespace Langlands.Global.FiniteCompletion

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

local instance completionValuativeRel : ValuativeRel (FiniteCompletion F v) :=
  valuativeRel v

/-- The canonical integers of the local-field realization are exactly the
original completed integers, as subsets of the original completion. -/
theorem mem_canonicalIntegers_iff (x : FiniteCompletion F v) :
    x ∈ 𝒪[FiniteCompletion F v] ↔ x ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation (FiniteCompletion F v)).vle_one_iff]
  change Valued.v x ≤ Valued.v (1 : FiniteCompletion F v) ↔ Valued.v x ≤ 1
  rw [map_one]

/-- Equality of the two actual subrings inside the completion. -/
theorem canonicalIntegers_eq :
    𝒪[FiniteCompletion F v] = (v.adicCompletionIntegers F).toSubring := by
  ext x
  exact mem_canonicalIntegers_iff v x

/-- The identity on completion elements identifies the canonical and original
integer rings. -/
def canonicalIntegersEquiv : 𝒪[FiniteCompletion F v] ≃+* v.adicCompletionIntegers F :=
  RingEquiv.subringCongr (canonicalIntegers_eq v)

@[simp] theorem canonicalIntegersEquiv_coe (x : 𝒪[FiniteCompletion F v]) :
    (canonicalIntegersEquiv v x : FiniteCompletion F v) = (x : FiniteCompletion F v) :=
  rfl

@[simp] theorem canonicalIntegersEquiv_symm_coe (x : v.adicCompletionIntegers F) :
    ((canonicalIntegersEquiv v).symm x : FiniteCompletion F v) =
      (x : FiniteCompletion F v) :=
  rfl

/-- The identity comparison respects the subtype topologies inherited from the
original finite completion. -/
def canonicalIntegersHomeomorph :
    𝒪[FiniteCompletion F v] ≃ₜ v.adicCompletionIntegers F where
  toEquiv := (canonicalIntegersEquiv v).toEquiv
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The two inclusions into the original completion commute with the comparison. -/
theorem canonicalIntegersEquiv_algebraMap (x : 𝒪[FiniteCompletion F v]) :
    algebraMap (v.adicCompletionIntegers F) (FiniteCompletion F v)
        (canonicalIntegersEquiv v x) =
      algebraMap 𝒪[FiniteCompletion F v] (FiniteCompletion F v) x :=
  rfl

/-- The induced comparison of the actual residue fields. -/
def canonicalResidueEquiv :
    𝓀[FiniteCompletion F v] ≃+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
  IsLocalRing.ResidueField.mapEquiv (canonicalIntegersEquiv v)

@[simp] theorem canonicalResidueEquiv_residue (x : 𝒪[FiniteCompletion F v]) :
    canonicalResidueEquiv v (IsLocalRing.residue 𝒪[FiniteCompletion F v] x) =
      IsLocalRing.residue (v.adicCompletionIntegers F) (canonicalIntegersEquiv v x) :=
  rfl

end Langlands.Global.FiniteCompletion
