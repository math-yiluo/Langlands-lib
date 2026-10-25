import Langlands.ClassFieldTheory.Local.NYLL.TypeZeroStatement

/-! # Universe transport targets for finite local reciprocity

These propositions ask for transport from each universe-zero host statement to
the same host statement at arbitrary independent field universes.
-/

namespace Langlands.LocalClassField.NYLL

universe u v w

/-- Transport finite reciprocity from universe zero to independent universes. -/
def FiniteAbelianReciprocityUniverseTransportStatement : Prop :=
  FiniteAbelianReciprocityTypeZeroStatement →
    Langlands.LocalClassField.FiniteAbelianReciprocity.{u, v}

/-- Transport the norm and transfer diagrams to independent universes. -/
def FiniteAbelianNormTransferUniverseTransportStatement : Prop :=
  FiniteAbelianNormTransferTypeZeroStatement →
    Langlands.LocalClassField.FiniteAbelianNormTransfer.{u, v, w}

/-- Transport the tower restriction diagram to independent universes. -/
def FiniteAbelianRestrictionUniverseTransportStatement : Prop :=
  FiniteAbelianRestrictionTypeZeroStatement →
    Langlands.LocalClassField.FiniteAbelianRestriction.{u, v, w}

end Langlands.LocalClassField.NYLL
