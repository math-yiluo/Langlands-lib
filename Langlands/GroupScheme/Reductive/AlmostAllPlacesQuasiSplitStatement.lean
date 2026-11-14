import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.Global.Adelic
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Quasi-splitness and torsor points at almost all places of a number field -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Global

namespace Langlands.GroupScheme

/-- Conrad, Exercise 5.5.3(iii), for number fields: a connected reductive group
over a number field `F` becomes quasi-split over the completion `F_v` at all but
finitely many finite places `v`, and every torsor under it acquires an
`F_v`-point at all but finitely many finite places `v`. -/
def AlmostAllPlacesQuasiSplitStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
      (∀ᶠ v in Filter.cofinite (α := FinitePlace F),
        IsQuasiSplit
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap F (FiniteCompletion F v))))).obj G)) ∧
      ∀ (X : Over (Spec (CommRingCat.of F))) [ModObj G.X X],
        Flat X.hom → Surjective X.hom → QuasiCompact X.hom →
        IsIso (ModObj.leftSMul G.X X) →
          ∀ᶠ v in Filter.cofinite (α := FinitePlace F),
            Nonempty (RingPoint F X (FiniteCompletion F v))

end Langlands.GroupScheme
