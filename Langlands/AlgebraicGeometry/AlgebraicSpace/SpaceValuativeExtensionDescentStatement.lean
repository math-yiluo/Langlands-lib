import Langlands.AlgebraicGeometry.AlgebraicSpace.DominatingValuativeLift

/-!
# Descent of a valuative lift along a dominating extension

Stacks Project, Morphisms of Algebraic Spaces, Lemma 67.41.4 (Tag 0ARH):
for a separated morphism, a supplied dominating-extension lift gives a lift
over the original valuation ring.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For a separated morphism, an existing valuative lift after a dominating
extension implies existence of a lift over the original valuation ring. -/
def SpaceValuativeExtensionDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsSeparatedMorphism f →
    ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (s : Spec (CommRingCat.of A) ⟶ S)
      (x : X.sections (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)))
      (y : Y.sections (Over.mk s)),
      mapSections f _ x =
          Y.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) y →
        HasDominatingValuativeLift f A K s x y →
        ∃ a : X.sections (Over.mk s),
          X.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) a = x ∧
            mapSections f _ a = y

end Langlands.AlgebraicGeometry.AlgebraicSpace
