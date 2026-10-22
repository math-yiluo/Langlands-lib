import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.Category.Subquotients
import Mathlib.RepresentationTheory.Semisimple

/-! Finite-type isolation of a cuspidal constituent on a determinant-unit Levi. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- The reduced block-isolation interface from BZ76 Lemma 3.26 and the proof
of Proposition 3.28, including the empty-product rank-zero extension. -/
def LeviCuspidalBlockIsolationTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (A D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      D.IsIrreducible → IsLeviCuspidal B D.representation →
      let ρD := determinantUnitRestriction T B D.representation
      Representation.IsSemisimpleRepresentation ρD ∧
      ∃ (m : ℕ) (V : Fin m → Subrepresentation ρD),
        (∀ i, Representation.IsIrreducible (V i).toRepresentation) ∧
        (⨆ i, (V i).toSubmodule) = ⊤ ∧
        ∃ (S Q : Subrepresentation A.representation),
          let ρS := determinantUnitRestriction T B S.toRepresentation
          IsCompl S.toSubmodule Q.toSubmodule ∧
          Representation.IsSemisimpleRepresentation ρS ∧
          (∀ W : Subrepresentation ρS,
            Representation.IsIrreducible W.toRepresentation →
            ∃ i : Fin m, Nonempty
              (W.toRepresentation.Equiv (V i).toRepresentation)) ∧
          ¬ SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q)

end Langlands.CuspidalSupport
