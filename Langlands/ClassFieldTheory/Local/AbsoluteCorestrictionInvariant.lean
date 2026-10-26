import Langlands.ClassFieldTheory.Local.AbsoluteCorestriction
import Langlands.ClassFieldTheory.Local.Invariants

/-!
# Compatibility of absolute corestriction with local invariants

This is a predicate on the raw invariant family. Its realization is a separate
existence statement; no invariant law is used to construct corestriction.
-/

namespace Langlands.ClassFieldTheory.Local

universe u v

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Genuine absolute corestriction preserves local invariants for every finite
compatible p-adic tower and every supplied compatible closure embedding. -/
def AbsoluteCorestriction (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F E : PadicField.{u} p) [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)],
    letI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    ∀ x : absoluteCohomology E.Carrier 2,
      I.absolute F (absoluteCorestriction F.Carrier E.Carrier 2 x) =
        I.absolute E x

end InvariantFamily

end Langlands.ClassFieldTheory.Local
