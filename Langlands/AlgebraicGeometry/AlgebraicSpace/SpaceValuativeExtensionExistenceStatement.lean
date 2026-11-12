import Langlands.AlgebraicGeometry.AlgebraicSpace.DominatingValuativeLift

/-!
# Existence of a valuative lift after a dominating extension

A separated specialization of Stacks Project, Morphisms of Algebraic Spaces,
Lemma 67.42.2(1) (Tag 0A3X), retaining the quasi-compactness hypothesis of the consumer.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact separated universally closed morphism of algebraic spaces
admits a valuative lift after a dominating extension of valuation rings. -/
def SpaceValuativeExtensionExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsQuasiCompactMorphism f → IsSeparatedMorphism f → IsUniversallyClosedMorphism f →
    ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (s : Spec (CommRingCat.of A) ⟶ S)
      (x : X.sections (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)))
      (y : Y.sections (Over.mk s)),
      mapSections f _ x =
          Y.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) y →
        HasDominatingValuativeLift f A K s x y

end Langlands.AlgebraicGeometry.AlgebraicSpace
