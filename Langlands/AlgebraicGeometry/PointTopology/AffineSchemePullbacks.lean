import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected

/-!
# Actual affine-scheme pullbacks and coordinate-algebra pushouts
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

private instance forgetAlgebra_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
  inferInstanceAs (PreservesColimitsOfShape WalkingSpan
    ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
      Under.forget (CommRingCat.of R)))

private instance forgetAlgebra_reflectsPushouts :
    ReflectsColimitsOfShape WalkingSpan (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
  inferInstanceAs (ReflectsColimitsOfShape WalkingSpan
    ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
      Under.forget (CommRingCat.of R)))

/-- The actual relative spectrum cone associated to an algebra pushout cocone. -/
def algebraSpectrumPullback {A B C : CommAlgCat.{u} R}
    {f : C ⟶ A} {g : C ⟶ B} (c : PushoutCocone f g) :
    PullbackCone (ringTestMap R f.hom) (ringTestMap R g.hom) :=
  PullbackCone.mk (ringTestMap R c.inl.hom) (ringTestMap R c.inr.hom) (by
    rw [← ringTestMap_comp, ← ringTestMap_comp]
    exact congrArg (fun k : C ⟶ c.pt => ringTestMap R k.hom) c.condition)

/-- An algebra pushout is a pullback of actual schemes over the specified base. -/
def algebraSpectrumPullbackIsLimit {A B C : CommAlgCat.{u} R}
    {f : C ⟶ A} {g : C ⟶ B} (c : PushoutCocone f g) (hc : IsColimit c) :
    IsLimit (algebraSpectrumPullback R c) := by
  have hring := (IsPushout.of_isColimit hc).map
    (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})
  have hscheme := isPullback_SpecMap_of_isPushout _ _ _ _ hring
  change IsPullback
    ((Over.forget _).map (ringTestMap R c.inl.hom))
    ((Over.forget _).map (ringTestMap R c.inr.hom))
    ((Over.forget _).map (ringTestMap R f.hom))
    ((Over.forget _).map (ringTestMap R g.hom)) at hscheme
  have hover : IsPullback (ringTestMap R c.inl.hom) (ringTestMap R c.inr.hom)
      (ringTestMap R f.hom) (ringTestMap R g.hom) :=
    hscheme.of_map_of_faithful (Over.forget (Spec (CommRingCat.of R)))
  exact hover.isLimit

variable {X Y Z : Over (Spec (CommRingCat.of R))}
variable [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]

/-- Global sections of an actual relative pullback cone give its coordinate
pushout cocone. -/
def affineCoordinatePushout {f : X ⟶ Z} {g : Y ⟶ Z}
    (c : PullbackCone f g) [IsAffine c.pt.left] :
    PushoutCocone (CommAlgCat.ofHom (affineCoordinatePullback R f))
      (CommAlgCat.ofHom (affineCoordinatePullback R g)) :=
  PushoutCocone.mk
    (CommAlgCat.ofHom (affineCoordinatePullback R c.fst))
    (CommAlgCat.ofHom (affineCoordinatePullback R c.snd)) (by
      apply CommAlgCat.hom_ext
      simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
      rw [← affineCoordinatePullback_comp, ← affineCoordinatePullback_comp, c.condition])

/-- An actual affine relative scheme pullback is a pushout of its actual
global-section algebras, retaining the specified base structure. -/
def affineCoordinatePushoutIsColimit {f : X ⟶ Z} {g : Y ⟶ Z}
    (c : PullbackCone f g) [IsAffine c.pt.left] (hc : IsLimit c) :
    IsColimit (affineCoordinatePushout R c) := by
  have hscheme := (IsPullback.of_isLimit hc).map
    (Over.forget (Spec (CommRingCat.of R)))
  have hspec : IsPullback (Spec.map c.fst.left.appTop) (Spec.map c.snd.left.appTop)
      (Spec.map f.left.appTop) (Spec.map g.left.appTop) :=
    hscheme.of_iso c.pt.left.isoSpec X.left.isoSpec Y.left.isoSpec Z.left.isoSpec
      (Scheme.isoSpec_hom_naturality c.fst.left).symm
      (Scheme.isoSpec_hom_naturality c.snd.left).symm
      (Scheme.isoSpec_hom_naturality f.left).symm
      (Scheme.isoSpec_hom_naturality g.left).symm
  have hop : IsPullback c.fst.left.appTop.op c.snd.left.appTop.op
      f.left.appTop.op g.left.appTop.op :=
    hspec.of_map_of_faithful Scheme.Spec
  have hring := hop.unop.flip
  have halg : IsPushout (CommAlgCat.ofHom (affineCoordinatePullback R f))
      (CommAlgCat.ofHom (affineCoordinatePullback R g))
      (CommAlgCat.ofHom (affineCoordinatePullback R c.fst))
      (CommAlgCat.ofHom (affineCoordinatePullback R c.snd)) :=
    hring.of_map_of_faithful (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})
  exact halg.isColimit

end Langlands.AlgebraicGeometry.PointTopology
