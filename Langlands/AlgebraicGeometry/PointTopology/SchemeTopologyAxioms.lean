import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyAxioms

/-!
# Topology families and source axioms for actual nonaffine points
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Arbitrary topologies on the actual points of all locally finite type schemes.
No compatibility or continuity property is assumed by this type. -/
def SchemePointTopologyFamily :=
  (X : Over (Spec (CommRingCat.of R))) → [LocallyOfFiniteType X.hom] →
    TopologicalSpace (RingPoint R X S)

/-- Restrict an arbitrary scheme-point topology assignment to affine schemes. -/
def schemePointTopologyFamilyToAffines (T : SchemePointTopologyFamily R S) :
    AffineSchemeTopologyFamily R S := fun X _ _ => T X

/-- The explicit affine-chart final topology, restricted to locally finite type schemes. -/
def evaluationSchemePointTopologyFamily [TopologicalSpace S] :
    SchemePointTopologyFamily R S := fun X _ => schemePointTopology R X S

/-- Actual postcomposition is continuous for every relative morphism. -/
def SchemePointTopologyFunctorial (T : SchemePointTopologyFamily R S) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y),
    @Continuous (RingPoint R X S) (RingPoint R Y S) (T X) (T Y) (fun p => p ≫ f)

/-- Actual relative pullback cones give compatible pairs with their subspace
product topology. The common point on the base of the cone is allowed to vary. -/
def SchemePointTopologyPullbacks (T : SchemePointTopologyFamily R S) : Prop :=
  ∀ (X Y Z : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g)
    [LocallyOfFiniteType c.pt.hom], IsLimit c →
    letI : TopologicalSpace (RingPoint R X S) := T X
    letI : TopologicalSpace (RingPoint R Y S) := T Y
    @IsHomeomorph (RingPoint R c.pt S)
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g}
      (T c.pt) inferInstance (affineSchemePullbackPointComparison R S c)

/-- Closed immersions induce embeddings; this axiom does not require closed images. -/
def SchemePointTopologyClosedImmersions (T : SchemePointTopologyFamily R S) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsClosedImmersion f.left],
    @IsEmbedding (RingPoint R X S) (RingPoint R Y S) (T X) (T Y) (fun p => p ≫ f)

/-- Open immersions induce open embeddings of the actual point map. -/
def SchemePointTopologyOpenImmersions (T : SchemePointTopologyFamily R S) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsOpenImmersion f.left],
    @IsOpenEmbedding (RingPoint R X S) (RingPoint R Y S) (T X) (T Y) (fun p => p ≫ f)

/-- The usual value-ring topology on the actual affine line, via its coordinate. -/
def SchemePointTopologyLine [TopologicalSpace S]
    (T : SchemePointTopologyFamily R S) : Prop :=
  @IsHomeomorph (RingPoint R (ringTest R (MvPolynomial Unit R)) S) S
    (T (ringTest R (MvPolynomial Unit R))) inferInstance
    (fun p => spectrumAlgebraPointEquiv R S (MvPolynomial Unit R) p
      (MvPolynomial.X ()))

/-- The five requirements in Conrad Proposition 3.1, with open and closed
immersions listed separately. They are assertions about an arbitrary assignment. -/
def SchemePointTopologyAxioms [TopologicalSpace S]
    (T : SchemePointTopologyFamily R S) : Prop :=
  SchemePointTopologyFunctorial R S T ∧
    SchemePointTopologyPullbacks R S T ∧
    SchemePointTopologyClosedImmersions R S T ∧
    SchemePointTopologyOpenImmersions R S T ∧
    SchemePointTopologyLine R S T

end Langlands.AlgebraicGeometry.PointTopology
