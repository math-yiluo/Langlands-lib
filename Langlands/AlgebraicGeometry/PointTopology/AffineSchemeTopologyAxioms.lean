import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Four topology axioms on actual finite-type affine scheme points
-/

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Functoriality on actual morphisms of finite-type affine schemes over the
specified base. -/
def AffineSchemeTopologyFunctorial (T : AffineSchemeTopologyFamily R S) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y),
    @Continuous (RingPoint R X S) (RingPoint R Y S) (T X) (T Y) (fun p => p ≫ f)

/-- Actual closed immersions induce embeddings. There is no closed-image or
Hausdorffness requirement in this axiom. -/
def AffineSchemeTopologyClosedImmersions
    (T : AffineSchemeTopologyFamily R S) : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsClosedImmersion f.left],
    @IsEmbedding (RingPoint R X S) (RingPoint R Y S) (T X) (T Y) (fun p => p ≫ f)

/-- All actual relative pullback cones give compatible-pair subspaces with
the product topology supplied by the two factor assignments. -/
def AffineSchemeTopologyPullbacks (T : AffineSchemeTopologyFamily R S) : Prop :=
  ∀ (X Y Z : Over (Spec (CommRingCat.of R)))
    [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g)
    [IsAffine c.pt.left] [LocallyOfFiniteType c.pt.hom], IsLimit c →
    letI : TopologicalSpace (RingPoint R X S) := T X
    letI : TopologicalSpace (RingPoint R Y S) := T Y
    @IsHomeomorph (RingPoint R c.pt S)
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g}
      (T c.pt) inferInstance (affineSchemePullbackPointComparison R S c)

/-- Normalization of the actual affine line by evaluation of its coordinate.
The single variable polynomial algebra is a concrete model of R[t]. -/
def AffineSchemeTopologyLine [TopologicalSpace S]
    (T : AffineSchemeTopologyFamily R S) : Prop :=
  @IsHomeomorph (RingPoint R (ringTest R (MvPolynomial Unit R)) S) S
    (T (ringTest R (MvPolynomial Unit R))) inferInstance
    (fun p => spectrumAlgebraPointEquiv R S (MvPolynomial Unit R) p
      (MvPolynomial.X ()))

/-- The four source axioms on actual finite-type affine scheme point spaces. -/
def AffineSchemeTopologyAxioms [TopologicalSpace S]
    (T : AffineSchemeTopologyFamily R S) : Prop :=
  AffineSchemeTopologyFunctorial R S T ∧
    AffineSchemeTopologyPullbacks R S T ∧
    AffineSchemeTopologyClosedImmersions R S T ∧
    AffineSchemeTopologyLine R S T

/-- The independently constructed global-section evaluation assignment
satisfies the four actual-scheme axioms. -/
def AffineSchemeTopologyExistenceProperty
    [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  AffineSchemeTopologyAxioms R S (evaluationAffineSchemeTopologyFamily R S)

/-- The two transports preserve the corresponding axioms; for assignments
satisfying the axioms they recover the original assignment. -/
def AffineSchemeTopologyTransportProperty
    [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  (∀ T : AffinePointTopologyFamily R S, AffineTopologyAxioms R S T →
    AffineSchemeTopologyAxioms R S (algebraTopologyFamilyToSchemes R S T) ∧
      schemeTopologyFamilyToAlgebras R S (algebraTopologyFamilyToSchemes R S T) = T) ∧
  (∀ T : AffineSchemeTopologyFamily R S, AffineSchemeTopologyAxioms R S T →
    AffineTopologyAxioms R S (schemeTopologyFamilyToAlgebras R S T) ∧
      algebraTopologyFamilyToSchemes R S (schemeTopologyFamilyToAlgebras R S T) = T)

/-- The source four axioms characterize the independently constructed
evaluation topology on actual finite-type affine scheme points. -/
def AffineSchemeTopologyCharacterizationProperty
    [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  ∀ T : AffineSchemeTopologyFamily R S, AffineSchemeTopologyAxioms R S T ↔
    T = evaluationAffineSchemeTopologyFamily R S

end Langlands.AlgebraicGeometry.PointTopology
