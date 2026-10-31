import Langlands.AbelianScheme.LieBaseChangeStatement
import Langlands.AbelianScheme.LieFunctor

/-! # Naturality of canonically characterized Lie base-change isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

/-- Any comparisons satisfying the published canonical equations intertwine the
actual Lie maps of every abelian-scheme homomorphism and its base change. -/
def LieBaseChangeNaturalityStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : T ⟶ S)
      (A B : AbelianScheme S) (f : A ⟶ B)
      (ellA : (pullback b).obj A.Lie ≅ ((baseChange b).obj A).Lie)
      (ellB : (pullback b).obj B.Lie ≅ ((baseChange b).obj B).Lie),
    IsIso (GroupScheme.cotangentBaseChangeMap b A.toGrp) →
    IsIso (GroupScheme.cotangentBaseChangeMap b B.toGrp) →
    ellA.hom ≫ dualMap (GroupScheme.cotangentBaseChangeMap b A.toGrp) =
        dualPullbackComparison b (GroupScheme.cotangentAtIdentity A.toGrp) →
    ellB.hom ≫ dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp) =
        dualPullbackComparison b (GroupScheme.cotangentAtIdentity B.toGrp) →
    (pullback b).map (lieMap f) ≫ ellB.hom =
      ellA.hom ≫ lieMap ((baseChange b).map f)

/-- The endomorphism specialization of canonical Lie naturality, applicable to
each endomorphism supplied by an actual order action. -/
def LieBaseChangeEndomorphismNaturalityStatement
    (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : T ⟶ S)
      (A : AbelianScheme S) (f : End A)
      (ell : (pullback b).obj A.Lie ≅ ((baseChange b).obj A).Lie),
    IsIso (GroupScheme.cotangentBaseChangeMap b A.toGrp) →
    ell.hom ≫ dualMap (GroupScheme.cotangentBaseChangeMap b A.toGrp) =
        dualPullbackComparison b (GroupScheme.cotangentAtIdentity A.toGrp) →
    (pullback b).map (lieMap f) ≫ ell.hom =
      ell.hom ≫ lieMap ((baseChange b).map f)

/-- Canonical Lie naturality for all actual homomorphisms, together with its
endomorphism specialization, as a single proof target. -/
def LieBaseChangeNaturalityStatements (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  LieBaseChangeNaturalityStatement S ∧
    LieBaseChangeEndomorphismNaturalityStatement S

end Langlands.AbelianScheme
