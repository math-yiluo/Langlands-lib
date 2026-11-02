import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.AffinePushoutPoints
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Coordinate-algebra axioms for affine point topologies
-/

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Functoriality is continuity of actual restriction maps on points. -/
def AffineTopologyFunctorial (T : AffinePointTopologyFamily R S) : Prop :=
  ∀ (A B : CommAlgCat.{u} R) [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (f : A ⟶ B),
    @Continuous (AlgPoint R B S) (AlgPoint R A S) (T B) (T A)
      (AlgPoint.precomp f.hom)

/-- A surjection of finite-type coordinate algebras gives an embedding of
actual point spaces. No closedness or Hausdorffness is imposed. -/
def AffineTopologyQuotientEmbeddings (T : AffinePointTopologyFamily R S) : Prop :=
  ∀ (A B : CommAlgCat.{u} R) [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (f : A ⟶ B), Function.Surjective f.hom →
    @IsEmbedding (AlgPoint R B S) (AlgPoint R A S) (T B) (T A)
      (AlgPoint.precomp f.hom)

/-- The single variable evaluates to the value ring with its given topology. -/
def AffineTopologyLine [TopologicalSpace S]
    (T : AffinePointTopologyFamily R S) : Prop :=
  @IsHomeomorph (AlgPoint R (MvPolynomial Unit R) S) S
    (T (CommAlgCat.of R (MvPolynomial Unit R))) inferInstance
    (fun p => p (MvPolynomial.X ()))

/-- Arbitrary pushouts of finite-type coordinate algebras give the actual
compatible-pair subspaces, expressing the affine fibre-product axiom. -/
def AffineTopologyPushouts (T : AffinePointTopologyFamily R S) : Prop :=
  ∀ (A B C : CommAlgCat.{u} R) [Algebra.FiniteType R A]
    [Algebra.FiniteType R B] [Algebra.FiniteType R C]
    (f : C ⟶ A) (g : C ⟶ B) (c : PushoutCocone f g)
    [Algebra.FiniteType R c.pt], IsColimit c →
    letI : TopologicalSpace (AlgPoint R A S) := T A
    letI : TopologicalSpace (AlgPoint R B S) := T B
    @IsHomeomorph (AlgPoint R c.pt S)
      {q : AlgPoint R A S × AlgPoint R B S //
        AlgPoint.precomp f.hom q.1 = AlgPoint.precomp g.hom q.2}
      (T c.pt) inferInstance (affinePushoutPointComparison R S c)

/-- Coordinate-algebra form of the source axioms used for uniqueness. -/
def AffineTopologyAxioms [TopologicalSpace S]
    (T : AffinePointTopologyFamily R S) : Prop :=
  AffineTopologyFunctorial R S T ∧
    AffineTopologyPushouts R S T ∧
    AffineTopologyQuotientEmbeddings R S T ∧
    AffineTopologyLine R S T

/-- The actual evaluation topology satisfies the four coordinate-algebra axioms. -/
def AffineTopologyExistenceProperty [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  AffineTopologyAxioms R S (evaluationAffineTopologyFamily R S)

/-- An assignment satisfying the coordinate-algebra axioms is the actual
evaluation assignment on every finite-type algebra. -/
def AffineTopologyUniquenessProperty [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  ∀ T : AffinePointTopologyFamily R S, AffineTopologyAxioms R S T →
    T = evaluationAffineTopologyFamily R S

/-- The coordinate-algebra axioms characterize the evaluation topology. -/
def AffineTopologyCharacterizationProperty [TopologicalSpace S] [IsTopologicalRing S] : Prop :=
  ∀ T : AffinePointTopologyFamily R S, AffineTopologyAxioms R S T ↔
    T = evaluationAffineTopologyFamily R S

end Langlands.AlgebraicGeometry.PointTopology
