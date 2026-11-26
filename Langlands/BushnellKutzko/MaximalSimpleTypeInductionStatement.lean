import Langlands.BushnellKutzko.SimpleTypeExtensionGroup
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Induction.OpenAdjunction

/-! # Compact induction from the group of a maximal simple type -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uρ uΛ uΛ' uπ

section Induction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} {ψF : AddChar F ℂ}
  {J : Subgroup (GeneralLinear n F)} {ρ : SmoothRep.{0, uF, uρ} ℂ J}

/-- An irreducible smooth representation of `Eˣ J` whose restriction to `J` contains the type. -/
def GLSimpleTypeData.IsInducingRepresentation (d : GLSimpleTypeData ψF ρ)
    (Λ : SmoothRep.{0, uF, uΛ} ℂ d.extensionSubgroup) : Prop :=
  Λ.IsIrreducible ∧ ContainsRepresentation Λ (Subgroup.inclusion d.le_extensionSubgroup) ρ

/-- Library compact induction of a representation of `Eˣ J`. The carrier is lifted to the
universe of compactly supported functions before applying the functor. -/
abbrev GLSimpleTypeData.compactInduce (d : GLSimpleTypeData ψF ρ)
    (Λ : SmoothRep.{0, uF, uΛ} ℂ d.extensionSubgroup) :
    SmoothRep.{0, uF, max uF uΛ} ℂ (GeneralLinear n F) :=
  (Induction.smoothCompactInduction.{0, uF, uΛ} ℂ d.extensionSubgroup).obj
    (SmoothRep.universeLift.{uF} Λ)

end Induction

/-- **BK93 (6.1.2) and (6.2.2).** For any exhibited simple type of period one, there exist
irreducible smooth representations of `Eˣ J` containing the type on restriction. Their compact
inductions are irreducible and supercuspidal, exhaust the irreducible representations containing
the type, and determine the inducing representation up to equivalence. -/
def MaximalSimpleTypeInductionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ) (J : Subgroup (GeneralLinear n F))
      (ρ : SmoothRep.{0, uF, uρ} ℂ J) (d : GLSimpleTypeData ψF ρ),
      d.period = 1 →
      (∃ Λ : SmoothRep.{0, uF, uΛ} ℂ d.extensionSubgroup, d.IsInducingRepresentation Λ) ∧
      (∀ Λ : SmoothRep.{0, uF, uΛ} ℂ d.extensionSubgroup, d.IsInducingRepresentation Λ →
        GeneralLinear.supercuspidalProperty (d.compactInduce Λ)) ∧
      (∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F),
        π.IsIrreducible → ContainsType π ρ →
        ∃ Λ : SmoothRep.{0, uF, uΛ} ℂ d.extensionSubgroup, d.IsInducingRepresentation Λ ∧
          Nonempty (π.representation.Equiv (d.compactInduce Λ).representation)) ∧
      ∀ (Λ : SmoothRep.{0, uF, uΛ} ℂ d.extensionSubgroup)
        (Λ' : SmoothRep.{0, uF, uΛ'} ℂ d.extensionSubgroup),
        d.IsInducingRepresentation Λ → d.IsInducingRepresentation Λ' →
        Nonempty ((d.compactInduce Λ).representation.Equiv (d.compactInduce Λ').representation) →
        Nonempty (Λ.representation.Equiv Λ'.representation)

end Langlands.BushnellKutzko
