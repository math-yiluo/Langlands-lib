import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Constructible
import Mathlib.SetTheory.Cardinal.Finite

/-! # Constructibility of every geometric connected-component count for schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The geometric point over `y` obtained from the algebraic closure of its residue field. -/
def componentCountGeometricPoint {Y : Scheme.{u}} (y : Y) :
    Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
    (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y

/-- The number of connected components of the actual geometric fibre, with `⊤` for an
infinite component set. -/
def geometricFiberComponentCount {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) : ℕ∞ :=
  ENat.card (ConnectedComponents (pullback f (componentCountGeometricPoint y) : Scheme.{u}))

/-- The scheme case of Conrad's Lemma 5.1, for every component count and arbitrary affine
base ring. This is a proposition target, not a proof. -/
def SchemeGeometricComponentCountConstructibleStatement : Prop :=
  ∀ (B : Type u) [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] (n : ℕ),
      IsConstructible {p | geometricFiberComponentCount f p = n}

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
