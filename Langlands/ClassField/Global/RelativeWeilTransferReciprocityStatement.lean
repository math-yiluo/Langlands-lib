import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.ClassField.Global.FundamentalClassStatement

/-! # Transfer reciprocity for relative global Weil groups

Proposition definition only. At the arithmetic fundamental classes, the transfer
`W_{E/F} → C_F` is surjective with kernel the commutator subgroup. It is not proved
here.
-/

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.ClassFieldTheory.Local

universe u

namespace RelativeWeilGroup

/-- For local invariant families forming class formations with the arithmetic
normalization, and global classes that are the corresponding fundamental classes, the
transfer `W_{E/F} → C_F` is surjective and its kernel is the commutator subgroup, so it
induces `W_{E/F}^{ab} ≅ C_F` (Artin–Tate XV Theorem 1; Tate 1979, §1.2). -/
def RelativeWeilTransferReciprocityStatement : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∀ c : FundamentalClass.ClassFamily.{u},
      FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
        FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c →
      ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
        [IsGalois F E],
        Function.Surjective (transfer c F E) ∧
          (transfer c F E).ker = commutator (RelativeWeilGroup c F E)

end RelativeWeilGroup

end Langlands.ClassField.Global
