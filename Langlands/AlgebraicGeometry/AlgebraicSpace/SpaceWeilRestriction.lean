import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionLocalTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates
import Mathlib.CategoryTheory.Sites.Over

/-!
# Weil restriction of fppf sheaves on schemes

For a morphism of schemes `g : S' ⟶ S`, the Weil restriction of a presheaf `F` on schemes
over `S'` is the presheaf `T ↦ F(T ×_S S')` on schemes over `S`: precomposition with the
pullback functor `Over.pullback g`. This functor is continuous for the fppf topologies,
so the Weil restriction of an fppf sheaf is an fppf sheaf. Along `Spec R' ⟶ Spec R`, the
`A`-valued points of the restriction are the `R' ⊗[R] A`-valued points of the original
sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (ringTest ringTestMap ringBaseChange ringBaseChangeSpectrumIso)
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section General

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- The Weil restriction of fppf sheaves along `g : S' ⟶ S`: an fppf sheaf `F` on schemes
over `S'` goes to the fppf sheaf `T ↦ F(T ×_S S')` on schemes over `S`. -/
def weilRestriction : FppfSheaf S' ⥤ FppfSheaf S :=
  (Over.pullback g).sheafPushforwardContinuous (Type (u + 1)) (fppfTopology S)
    (fppfTopology S')

/-- The sections of the Weil restriction over `T` are the sections over `T ×_S S'`. -/
theorem weilRestriction_obj_obj (F : FppfSheaf S') (T : Over S) :
    ((weilRestriction g).obj F).obj.obj (op T) =
      F.obj.obj (op ((Over.pullback g).obj T)) :=
  rfl

/-- The Weil restriction of a morphism of fppf sheaves acts on sections over `T` as the
original morphism on sections over `T ×_S S'`. -/
theorem weilRestriction_map_hom_app {F G : FppfSheaf S'} (f : F ⟶ G) (T : Over S) :
    ((weilRestriction g).map f).hom.app (op T) =
      f.hom.app (op ((Over.pullback g).obj T)) :=
  rfl

end General

section Ring

/-- Finite presentation over an affine base `Spec C`: an étale surjective atlas by an actual
scheme that is locally of finite presentation and quasi-compact over `Spec C`. -/
def FinitePresentationOverRing (C : Type u) [CommRing C]
    (X : AlgebraicSpace (Spec (CommRingCat.of C))) : Prop :=
  HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']

/-- Conrad's `Res_{R'/R}`: Weil restriction of fppf sheaves along
`Spec R' ⟶ Spec R`. -/
abbrev ringWeilRestriction :
    FppfSheaf (Spec (CommRingCat.of R')) ⥤ FppfSheaf (Spec (CommRingCat.of R)) :=
  weilRestriction (Spec.algebraMap R R')

/-- The Weil restriction `Res_{R'/R}(X')` of an algebraic space `X'` over `Spec R'`, as an
algebraic space over `Spec R`, given that its underlying fppf sheaf is one. -/
def ringWeilRestrictionSpace (X' : AlgebraicSpace (Spec (CommRingCat.of R')))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf)) :
    AlgebraicSpace (Spec (CommRingCat.of R)) :=
  ⟨(ringWeilRestriction R R').obj X'.toSheaf, h⟩

/-- The morphism `Res_{R'/R}(X') ⟶ Res_{R'/R}(Y')` induced by `f : X' ⟶ Y'`. -/
def ringWeilRestrictionSpaceMap {X' Y' : AlgebraicSpace (Spec (CommRingCat.of R'))}
    (hX : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf))
    (hY : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj Y'.toSheaf)) (f : X' ⟶ Y') :
    ringWeilRestrictionSpace R R' X' hX ⟶ ringWeilRestrictionSpace R R' Y' hY :=
  homMk ((ringWeilRestriction R R').map f.hom).hom

variable (A : Type u) [CommRing A] [Algebra R A]

/-- The points `Res_{R'/R}(X')(A) = X'(R' ⊗[R] A)`, by pulling back along the canonical
isomorphism `Spec A ×_{Spec R} Spec R' ≅ Spec (R' ⊗[R] A)` over `Spec R'`. -/
def ringWeilRestrictionPointsEquiv (X' : AlgebraicSpace (Spec (CommRingCat.of R')))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf)) :
    RingPoints R (ringWeilRestrictionSpace R R' X' h) A ≃ RingPoints R' X' (R' ⊗[R] A) :=
  (X'.presheaf.mapIso (ringBaseChangeSpectrumIso R R' A).op).toEquiv.symm

theorem ringWeilRestrictionPointsEquiv_apply
    (X' : AlgebraicSpace (Spec (CommRingCat.of R')))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf))
    (x : RingPoints R (ringWeilRestrictionSpace R R' X' h) A) :
    ringWeilRestrictionPointsEquiv R R' A X' h x =
      X'.pullback (ringBaseChangeSpectrumIso R R' A).inv x :=
  rfl

/-- The point identification is natural in morphisms of algebraic spaces. -/
theorem ringWeilRestrictionPointsEquiv_map
    {X' Y' : AlgebraicSpace (Spec (CommRingCat.of R'))}
    (hX : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf))
    (hY : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj Y'.toSheaf)) (f : X' ⟶ Y')
    (x : RingPoints R (ringWeilRestrictionSpace R R' X' hX) A) :
    ringWeilRestrictionPointsEquiv R R' A Y' hY
        (RingPoints.map (ringWeilRestrictionSpaceMap R R' hX hY f) x) =
      RingPoints.map f (ringWeilRestrictionPointsEquiv R R' A X' hX x) :=
  mapSections_naturality f (ringBaseChangeSpectrumIso R R' A).inv x

/-- Conrad's identification `Res_{R'/R}(X')(R) = X'(R')` of rational points. -/
def ringWeilRestrictionBasePointsEquiv (X' : AlgebraicSpace (Spec (CommRingCat.of R')))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf)) :
    RingPoints R (ringWeilRestrictionSpace R R' X' h) R ≃ RingPoints R' X' R' :=
  (ringWeilRestrictionPointsEquiv R R' R X' h).trans
    (X'.presheaf.mapIso (PointTopology.weilRestrictionTensorUnitTestIso R R').op).toEquiv

end Ring

end Langlands.AlgebraicGeometry.AlgebraicSpace
