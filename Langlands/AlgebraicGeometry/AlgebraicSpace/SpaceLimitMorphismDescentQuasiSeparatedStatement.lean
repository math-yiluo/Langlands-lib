import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Morphisms of quasi-separated algebraic spaces along cofiltered limits of affine schemes

Conrad, printed p.13: Theorem 3.4 holds with finitely presented algebraic spaces in place of
finitely presented schemes. This file states the descent of morphisms out of a
quasi-separated space: a morphism between the base changes of two algebraic spaces to the
limit of a cofiltered diagram of affine schemes comes from a morphism between their base
changes to some stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Morphism descent for algebraic spaces along a cofiltered limit of affine schemes over an
affine base. The source is quasi-separated and has a quasi-compact atlas; the target has a
locally finitely presented atlas. Every morphism between the base changes to the limit
agrees, on every test scheme over the limit, with the base change of a morphism at some
stage. -/
def SpaceLimitMorphismDescentQuasiSeparated : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (S : Scheme.{u}) [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (X Z : AlgebraicSpace S),
    IsQuasiSeparated X → HasAtlasProperty (@QuasiCompact.{u}) X →
    LocallyOfFinitePresentationOverBase Z →
    ∀ φ : baseChange p X ⟶ baseChange p Z,
      ∃ (i : I) (φi : baseChange (t.app i) X ⟶ baseChange (t.app i) Z),
        ∀ (W : Over c.pt) (x : (baseChange p X).sections W),
          mapSections φ W x =
            Z.pullback
              (Over.homMk (𝟙 W.left) (by simp [← hp i]) :
                (Over.map p).obj W ⟶ (Over.map (t.app i)).obj ((Over.map (c.π.app i)).obj W))
              (mapSections φi ((Over.map (c.π.app i)).obj W)
                (X.pullback
                  (Over.homMk (𝟙 W.left) (by simp [← hp i]) :
                    (Over.map (t.app i)).obj ((Over.map (c.π.app i)).obj W) ⟶
                      (Over.map p).obj W) x))

end Langlands.AlgebraicGeometry.AlgebraicSpace
