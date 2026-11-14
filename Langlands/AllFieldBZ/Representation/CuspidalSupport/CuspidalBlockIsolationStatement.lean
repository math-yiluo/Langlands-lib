import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviCuspidalBlockIsolationTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
universe uF uV

/-- The reduced block-isolation interface from BZ76 Lemma 3.26 and the proof
of Proposition 3.28, including the empty-product rank-zero extension. -/
def LeviCuspidalBlockIsolationTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
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

end Langlands.AllFieldBZ.CuspidalSupport
