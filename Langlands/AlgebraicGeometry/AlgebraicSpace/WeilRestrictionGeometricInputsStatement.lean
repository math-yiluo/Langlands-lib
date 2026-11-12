import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction

/-! # Geometric inputs for restriction of scalars of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The diagonal input for Conrad's Lemma 5.10: restriction along a finite projective
algebra carries a quasi-compact space diagonal to a representable quasi-compact diagonal,
and a closed space diagonal to a representable closed diagonal. The restricted sheaf
is not assumed to be an algebraic space. -/
def WeilRestrictionDiagonalStatement : Prop :=
  ∀ (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Module.Projective R R'] (X' : AlgebraicSpace (Spec (CommRingCat.of R'))),
    IsQuasiSeparated X' →
      (MorphismProperty.inverseImage (@QuasiCompact.{u})
        (Over.forget (Spec (CommRingCat.of R)))).relative
          (schemeYoneda _) (diag ((ringWeilRestriction R R').obj X'.toSheaf).obj) ∧
      (IsSeparated X' →
        IsClosedImmersion (diag ((ringWeilRestriction R R').obj X'.toSheaf).obj))

/-- The affine-atlas input for Conrad's Lemma 5.10: restriction along a finite projective
algebra preserves the étale and surjective properties of a finite-type affine scheme atlas
of a quasi-separated algebraic space. The properties concern the actual transformation
of full restricted presheaves, without assuming representability of the target. -/
def WeilRestrictionAffineEtaleAtlasStatement : Prop :=
  ∀ (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Module.Projective R R'] (X' : AlgebraicSpace (Spec (CommRingCat.of R'))),
    IsQuasiSeparated X' →
    ∀ (U' : Over (Spec (CommRingCat.of R'))) [IsAffine U'.left]
      [LocallyOfFiniteType U'.hom] (a : (schemeYoneda _).obj U' ⟶ X'.presheaf),
      IsEtale a → IsSurjective a →
        IsEtale (Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a) ∧
          IsSurjective (Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a)

end Langlands.AlgebraicGeometry.AlgebraicSpace
