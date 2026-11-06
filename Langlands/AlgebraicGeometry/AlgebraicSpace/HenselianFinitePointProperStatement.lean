import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Finite maps of algebraic spaces are proper on rational points

Conrad's Corollary 5.12: over a henselian valued field `K` that is algebraically closed in
its completion, a finite map between separated algebraic spaces locally of finite type
induces a topologically proper map on rational points. The remark after the corollary:
the hypothesis on `K` holds in characteristic zero.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Corollary 5.12 (printed p.20): let `K` be a henselian valued field that is
algebraically closed in its completion `K̂`. For a finite map `f : X ⟶ Y` between
separated algebraic spaces locally of finite type over `Spec K`, the induced map
`X(K) → Y(K)` is a proper map for the étale-chart topologies. -/
def HenselianFinitePointProperStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    algebraicClosure K (UniformSpace.Completion K) = ⊥ →
    ∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of K))) (f : X ⟶ Y),
      IsSeparated X → LocallyOfFiniteTypeOverBase X →
      IsSeparated Y → LocallyOfFiniteTypeOverBase Y →
      IsFinite (hom f) →
        @IsProperMap _ _ (etaleChartTopology K X) (etaleChartTopology K Y)
          (RingPoints.map (A := K) f)

/-- The characteristic-zero case of Conrad's remark after Corollary 5.12 (printed p.20):
a henselian valued field of characteristic zero is algebraically closed in its
completion. -/
def HenselianCharZeroAlgebraicallyClosedInCompletionStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K → CharZero K →
    algebraicClosure K (UniformSpace.Completion K) = ⊥

end Langlands.AlgebraicGeometry.AlgebraicSpace
