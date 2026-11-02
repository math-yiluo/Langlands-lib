import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Closed representability targets for fixed subgroups and centralizers -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A closed subgroup scheme represents the given subgroup functor on all tests. -/
def IsClosedRepresentable (F : SubgroupFunctor G) : Prop :=
  ∃ (C : GroupScheme S) (i : C ⟶ G), F.IsRepresentedBy i ∧ IsClosedSubgroup i

end SubgroupFunctor

/-- The coordinate module of `H` becomes projective after a faithfully flat
extension of the base ring. Affineness and flatness of `H` are separate premises. -/
def HasFpqcProjectiveCoordinateModule {R : CommRingCat.{u}}
    (H : GroupScheme (Spec R)) : Prop :=
  ∃ B : CommAlgCat.{u} R, Module.FaithfullyFlat R B ∧
    Module.Projective B (B ⊗[R] ((algΓ R).obj H.X).unop)

/-- CGP A.8.10(1), specialized to actions by group automorphisms: the all-test
fixed subgroup has a closed representative. -/
def FixedSubgroupRepresentabilityStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (H G : GroupScheme (Spec R)),
    IsAffineHom H.X.hom → Flat H.X.hom →
    HasFpqcProjectiveCoordinateModule H → IsSeparated G.X.hom →
    ∀ a : AutomorphicAction H G, a.fixedSubgroup.IsClosedRepresentable

/-- Over a field, an affine acting group has a closed fixed subgroup for every
automorphic action. The acting group need not be smooth or of finite type. -/
def FieldFixedSubgroupRepresentabilityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom H.X.hom →
    ∀ a : AutomorphicAction H G, a.fixedSubgroup.IsClosedRepresentable

/-- The all-test centralizer of any homomorphism from an affine commutative
group over a field is a closed subgroup scheme, including for nonsmooth sources. -/
def FieldCentralizerRepresentabilityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom H.X.hom →
    ∀ j : H.toGrp ⟶ G, (torusCentralizer j).IsClosedRepresentable

end Langlands.GroupScheme
