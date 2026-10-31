import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Reducedness of a group scheme from its identity stalk -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A locally finite type group scheme over an algebraically closed field is reduced
if its local ring at the identity is reduced. This is a proposition definition. -/
def AlgClosedFieldReducedOfOriginStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (P : Over (Spec (CommRingCat.of k))) [GrpObj P],
    LocallyOfFiniteType P.hom →
      _root_.IsReduced
        (P.left.presheaf.stalk ((η[P]).left (IsLocalRing.closedPoint k))) →
      AlgebraicGeometry.IsReduced P.left

end Langlands.GroupScheme
