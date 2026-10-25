import Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement

/-! # Universe-zero finite reciprocity targets

These transparent aliases specialize the existing host propositions to fields
whose carriers lie in `Type 0`. They provide statement targets, not proofs.
-/

namespace Langlands.LocalClassField.NYLL

/-- The host finite reciprocity proposition at field universes zero. -/
abbrev FiniteAbelianReciprocityTypeZeroStatement : Prop :=
  Langlands.LocalClassField.FiniteAbelianReciprocity.{0, 0}

/-- The host finite norm and transfer proposition at field universes zero. -/
abbrev FiniteAbelianNormTransferTypeZeroStatement : Prop :=
  Langlands.LocalClassField.FiniteAbelianNormTransfer.{0, 0, 0}

/-- The host finite tower restriction proposition at field universes zero. -/
abbrev FiniteAbelianRestrictionTypeZeroStatement : Prop :=
  Langlands.LocalClassField.FiniteAbelianRestriction.{0, 0, 0}

end Langlands.LocalClassField.NYLL
