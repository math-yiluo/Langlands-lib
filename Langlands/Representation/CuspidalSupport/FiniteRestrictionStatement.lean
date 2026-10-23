import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Mathlib.RepresentationTheory.Semisimple

/-! Finite irreducible restriction to the determinant-unit subgroup of a product Levi. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- The reduced spanning form of BZ76 Lemma 3.26: the restriction of an irreducible
smooth complex representation of a product Levi to its determinant-unit subgroup is
semisimple and is spanned by finitely many irreducible subrepresentations. Rank zero
is the elementary empty-product extension. -/
def LeviFiniteRestrictionTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier), D.IsIrreducible →
      let ρD := determinantUnitRestriction T B D.representation
      Representation.IsSemisimpleRepresentation ρD ∧
      ∃ (m : ℕ) (V : Fin m → Subrepresentation ρD),
        (∀ i, Representation.IsIrreducible (V i).toRepresentation) ∧
        (⨆ i, (V i).toSubmodule) = ⊤

end Langlands.CuspidalSupport
