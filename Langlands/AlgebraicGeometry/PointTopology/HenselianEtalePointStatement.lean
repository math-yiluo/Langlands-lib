import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Étale maps on rational points over henselian valued fields

Conrad's henselian valued fields, the separable closedness of such a field in its
completion, and the local homeomorphism property of étale maps on actual rational
points with the affine-chart point topology.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Conrad's henselian valued field: the absolute value given by the norm of a
nontrivially normed field extends uniquely to every algebraic extension field. -/
def IsHenselianValuedField (K : Type u) [NontriviallyNormedField K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L],
    ∃! v : AbsoluteValue L ℝ, ∀ x : K, v (algebraMap K L x) = ‖x‖

/-- A henselian valued field is separably algebraically closed in its completion. -/
def HenselianSeparablyClosedInCompletionStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    separableClosure K (UniformSpace.Completion K) = ⊥

/-- Conrad's Lemma 5.3: over a henselian valued field, an étale map between locally
finite type schemes induces a local homeomorphism on rational points. -/
def HenselianEtalePointLocalHomeomorphStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    ∀ (X Y : Over (Spec (CommRingCat.of K)))
      [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) [Etale f.left],
      letI : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
      letI : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
      IsLocalHomeomorph (X := RingPoint K X K) (Y := RingPoint K Y K)
        (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K))

/-- The two henselian assertions of Conrad's printed p.14. -/
def HenselianEtalePointStatement : Prop :=
  HenselianSeparablyClosedInCompletionStatement.{u} ∧
    HenselianEtalePointLocalHomeomorphStatement.{u}

end Langlands.AlgebraicGeometry.PointTopology
