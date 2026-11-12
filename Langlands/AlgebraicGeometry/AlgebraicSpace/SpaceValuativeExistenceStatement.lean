import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# The valuative criterion for separated universally closed morphisms of algebraic spaces

Stacks Project, Morphisms of Algebraic Spaces, Lemma 67.42.3 (Tag 0A3Y), implication
(1) ⇒ (3): for a quasi-compact separated morphism of algebraic spaces that is universally
closed, every commutative square from `Spec K → Spec A`, with `A` a valuation ring with
fraction field `K`, has a diagonal lift `Spec A → X`. No extension of `K` is needed.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Stacks Project, Morphisms of Algebraic Spaces, Lemma 67.42.3 (Tag 0A3Y), (1) ⇒ (3): let
`f : X ⟶ Y` be a quasi-compact separated morphism of algebraic spaces over a scheme `S`. If
`f` is universally closed, then for every valuation ring `A` with fraction field `K`, every
morphism `s : Spec A ⟶ S`, every section `x` of `X` over `Spec K` (structure morphism
`Spec K ⟶ Spec A ⟶ S`) and every section `y` of `Y` over `Spec A` with
`f(x) = y|_{Spec K}`, there is a section `a` of `X` over `Spec A` with `a|_{Spec K} = x` and
`f(a) = y`. -/
def SpaceValuativeExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsQuasiCompactMorphism f → IsSeparatedMorphism f → IsUniversallyClosedMorphism f →
    ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (s : Spec (CommRingCat.of A) ⟶ S)
      (x : X.sections (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)))
      (y : Y.sections (Over.mk s)),
      mapSections f _ x =
          Y.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) y →
        ∃ a : X.sections (Over.mk s),
          X.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) a = x ∧
            mapSections f _ a = y

end Langlands.AlgebraicGeometry.AlgebraicSpace
