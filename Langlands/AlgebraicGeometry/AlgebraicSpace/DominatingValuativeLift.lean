import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceStatement

/-!
# Valuative lifts after a dominating extension

The extension diagram in Stacks Project, Morphisms of Algebraic Spaces,
Definition 67.41.1 (Tag 03IX), encoded using sections of the actual algebraic spaces.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The supplied valuative square has a lift after an arbitrary extension of its
fraction field and a dominating extension of its valuation ring. -/
def HasDominatingValuativeLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (s : Spec (CommRingCat.of A) ⟶ S)
    (x : X.sections (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)))
    (y : Y.sections (Over.mk s)) : Prop :=
  ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : ValuationRing B)
    (L : Type u) (_ : Field L) (_ : Algebra B L) (_ : IsFractionRing B L)
    (i : A →+* B) (_ : IsLocalHom i) (j : K →+* L)
    (hij : (algebraMap B L).comp i = j.comp (algebraMap A K))
    (a : X.sections (Over.mk (Spec.map (CommRingCat.ofHom i) ≫ s))),
    X.pullback
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap B L)))
          (by
            simp only [Over.mk_hom, ← Category.assoc, ← Spec.map_comp,
              ← CommRingCat.ofHom_comp, hij]) :
          Over.mk (Spec.map (CommRingCat.ofHom j) ≫
            Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom i) ≫ s)) a =
      X.pullback
        (Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom j) ≫
            Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)) x ∧
      mapSections f _ a =
        Y.pullback (Over.homMk (Spec.map (CommRingCat.ofHom i)) rfl) y

end Langlands.AlgebraicGeometry.AlgebraicSpace
