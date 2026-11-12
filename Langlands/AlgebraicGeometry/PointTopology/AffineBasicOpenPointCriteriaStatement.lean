import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Basic open subschemes and points over a topological ring

Conrad, printed pp.3–4: for an affine `X = Spec A` of finite type over a topological ring `R`
and a basic open `U = Spec A_f`, the points `U(R)` form the locus in `X(R)` where `f` takes
unit values. Their openness for all such `U` is equivalent to openness of the units of `R`,
the map `U(R) → X(R)` is a topological embedding for all such `U` exactly when the units carry
the subspace topology, and these are the only obstacles to basic opens giving open embeddings.
-/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The map on points induced by the basic open `Spec A_f → Spec A`: precomposition with the
localization map `A → A_f`. -/
abbrev basicOpenPointMap (R S A : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [Algebra R A] (f : A) :
    AlgPoint R (Localization.Away f) S → AlgPoint R A S :=
  AlgPoint.precomp (IsScalarTower.toAlgHom R A (Localization.Away f))

/-- Conrad's discussion of basic opens (printed pp.3–4), for every commutative topological ring
`S` over a commutative ring `R`, with the evaluation topologies on algebra points:

1. the image of `Spec A_f`-points in `Spec A`-points is the locus where `f` is a unit;
2. these images are open for all finite-type `A` and all `f` iff the units of `S` are open;
3. the maps are topological embeddings for all finite-type `A` and all `f` iff `Sˣ → S` is a
   topological embedding (the units, with their topology from `(s, s⁻¹)`, carry the subspace
   topology);
4. the maps are open embeddings for all finite-type `A` and all `f` iff `Sˣ → S` is an open
   embedding. -/
def AffineBasicOpenPointCriteria : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S],
    (∀ (A : Type u) [CommRing A] [Algebra R A] (f : A),
      Set.range (basicOpenPointMap R S A f) = {p : AlgPoint R A S | IsUnit (p f)}) ∧
    ((∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (f : A),
        IsOpen (Set.range (basicOpenPointMap R S A f))) ↔ IsOpen {s : S | IsUnit s}) ∧
    ((∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (f : A),
        Topology.IsEmbedding (basicOpenPointMap R S A f)) ↔
      Topology.IsEmbedding (Units.val : Sˣ → S)) ∧
    ((∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (f : A),
        Topology.IsOpenEmbedding (basicOpenPointMap R S A f)) ↔
      Topology.IsOpenEmbedding (Units.val : Sˣ → S))

end Langlands.AlgebraicGeometry.PointTopology
