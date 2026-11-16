import Langlands.GroupScheme.AffineGmAttractingLimit
import Langlands.GroupScheme.ImageGenerationActions

/-! # Maps on fixed and attracting schemes of affine multiplicative-group actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X Y : Over S}
  (s : PointwiseSchemeAction H X) (t : PointwiseSchemeAction H Y)

/-- An equivariant morphism preserves fixedness on all refinements. -/
theorem IsEquivariant.map_isFixed {f : X ⟶ Y} (hf : s.IsEquivariant t f)
    {T : Over S} {x : T ⟶ X} (hx : s.IsFixed x) : t.IsFixed (x ≫ f) := by
  intro V b h
  rw [← Category.assoc, ← hf, hx]

variable {X Y : Over S}
  (s : PointwiseSchemeAction (Gm S).toGrp X)
  (t : PointwiseSchemeAction (Gm S).toGrp Y)

/-- An equivariant morphism takes an orbit to the orbit of its image. -/
theorem IsEquivariant.orbit_comp {f : X ⟶ Y} (hf : s.IsEquivariant t f)
    {T : Over S} (x : T ⟶ X) : s.orbit x ≫ f = t.orbit (x ≫ f) := by
  rw [orbit, hf, orbit, Category.assoc]

/-- An equivariant morphism preserves actual affine-line orbit extensions. -/
theorem IsEquivariant.map_isAttracted {f : X ⟶ Y} (hf : s.IsEquivariant t f)
    {T : Over S} {x : T ⟶ X} (hx : s.IsAttracted x) : t.IsAttracted (x ≫ f) := by
  obtain ⟨E, hE⟩ := hx
  exact ⟨E ≫ f, by rw [← Category.assoc, hE, PointwiseSchemeAction.IsEquivariant.orbit_comp s t hf]⟩

end PointwiseSchemeAction

namespace AffineSchemeCoordinates

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}
  [IsAffine X.left] [IsAffine Y.left]

/-- The contravariant coordinate map of the supplied actual morphism. -/
def map (f : X ⟶ Y) : algebra Y ⟶ algebra X :=
  (pointEquiv Y (algebra X)).symm ((schemeIso X).hom ≫ f)

/-- The coordinate map recovers the original morphism. -/
theorem pointEquiv_map (f : X ⟶ Y) :
    pointEquiv Y (algebra X) (map f) = (schemeIso X).hom ≫ f :=
  Equiv.apply_symm_apply _ _

/-- Every coordinate point is transported by the same supplied morphism. -/
theorem pointEquiv_map_comp (f : X ⟶ Y) {C : CommAlgCat.{u} R}
    (x : algebra X ⟶ C) :
    pointEquiv Y C (map f ≫ x) = pointEquiv X C x ≫ f := by
  rw [pointEquiv_comp, pointEquiv_map, ← Category.assoc]
  rfl

/-- The spectrum of the coordinate map is the actual morphism in coordinates. -/
theorem algSpec_map (f : X ⟶ Y) :
    (algSpec R).map (map f).op = (schemeIso X).hom ≫ f ≫ (schemeIso Y).inv := by
  apply (cancel_mono (schemeIso Y).hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact pointEquiv_map f

/-- Smoothness of the actual affine morphism gives smoothness of its coordinate map. -/
theorem smooth_map (f : X ⟶ Y) (hf : Smooth f.left) : (map f).hom.toRingHom.Smooth := by
  let : IsIso (schemeIso X).hom.left :=
    ((Over.forget (Spec R)).mapIso (schemeIso X)).isIso_hom
  let : IsIso (schemeIso Y).inv.left :=
    ((Over.forget (Spec R)).mapIso (schemeIso Y)).isIso_inv
  have h : Smooth ((algSpec R).map (map f).op).left := by
    rw [algSpec_map]
    change Smooth ((schemeIso X).hom.left ≫ f.left ≫ (schemeIso Y).inv.left)
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h

end AffineSchemeCoordinates

namespace GmCoordinateAction

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}
  [IsAffine X.left] [IsAffine Y.left]
  (s : PointwiseSchemeAction (Gm (Spec R)).toGrp X)
  (t : PointwiseSchemeAction (Gm (Spec R)).toGrp Y)
  {f : X ⟶ Y} (hf : s.IsEquivariant t f)

include hf

/-- The coordinate map commutes with the natural unit actions. -/
theorem coordinateMap_act {C : CommAlgCat.{u} R} (z : Cˣ)
    (x : AffineSchemeCoordinates.algebra X ⟶ C) :
    AffineSchemeCoordinates.map f ≫ (ofPointwiseSchemeAction s).act z x =
      (ofPointwiseSchemeAction t).act z (AffineSchemeCoordinates.map f ≫ x) := by
  apply (AffineSchemeCoordinates.pointEquiv Y C).injective
  rw [AffineSchemeCoordinates.pointEquiv_map_comp, pointEquiv_schemeAct,
    pointEquiv_schemeAct, AffineSchemeCoordinates.pointEquiv_map_comp, hf]

/-- Actual equivariance gives equivariance of the Laurent coactions. -/
theorem coordinateMap_coaction :
    AffineSchemeCoordinates.map f ≫ coaction (ofPointwiseSchemeAction s) =
      coaction (ofPointwiseSchemeAction t) ≫ coefficientMap (AffineSchemeCoordinates.map f) := by
  rw [coaction, coordinateMap_act s t hf, act_universal]

/-- The actual map induced on the all-test fixed schemes. -/
def schemeActionFixedMap : schemeActionFixedScheme s ⟶ schemeActionFixedScheme t :=
  ((exists_schemeActionFixed_factor_iff_all t (schemeActionFixedHom s ≫ f)).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isFixed s t hf (schemeActionFixedHom_isFixed s))).choose

/-- The fixed-scheme map lies over the original equivariant morphism. -/
theorem schemeActionFixedMap_comp :
    schemeActionFixedMap s t hf ≫ schemeActionFixedHom t = schemeActionFixedHom s ≫ f :=
  ((exists_schemeActionFixed_factor_iff_all t (schemeActionFixedHom s ≫ f)).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isFixed s t hf (schemeActionFixedHom_isFixed s))).choose_spec

/-- The actual map induced on the all-test attracting schemes. -/
def schemeActionAttractingMap :
    schemeActionAttractingScheme s ⟶ schemeActionAttractingScheme t :=
  ((exists_schemeActionAttracting_factor_iff_all t (schemeActionAttractingHom s ≫ f)).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isAttracted s t hf (schemeActionAttractingHom_isAttracted s))).choose

/-- The attracting-scheme map lies over the original equivariant morphism. -/
theorem schemeActionAttractingMap_comp :
    schemeActionAttractingMap s t hf ≫ schemeActionAttractingHom t =
      schemeActionAttractingHom s ≫ f :=
  ((exists_schemeActionAttracting_factor_iff_all t (schemeActionAttractingHom s ≫ f)).mpr
    (PointwiseSchemeAction.IsEquivariant.map_isAttracted s t hf (schemeActionAttractingHom_isAttracted s))).choose_spec

/-- The induced attracting map preserves evaluation at zero. -/
theorem schemeActionAttractingMap_comp_zero :
    schemeActionAttractingMap s t hf ≫ schemeActionAttractingZero t =
      schemeActionAttractingZero s ≫ f := by
  rw [schemeActionAttractingZero_naturality t (schemeActionAttractingMap s t hf)
    (schemeActionAttractingMap_comp s t hf)
    (show schemeActionAttractingScheme s ◁ AffineLine.unitInclusion (Spec R) ≫
        (schemeActionAttractingExtension s ≫ f) =
      t.orbit (schemeActionAttractingHom s ≫ f) by
      rw [← Category.assoc, schemeActionAttractingExtension_restrict, PointwiseSchemeAction.IsEquivariant.orbit_comp s t hf])]
  rfl

/-- The actual attracting-to-fixed limit commutes with equivariant morphisms. -/
theorem schemeActionAttractingMap_comp_limit :
    schemeActionAttractingMap s t hf ≫ schemeActionAttractingLimit t =
      schemeActionAttractingLimit s ≫ schemeActionFixedMap s t hf := by
  apply (cancel_mono (schemeActionFixedHom t)).mp
  rw [Category.assoc, schemeActionAttractingLimit_comp,
    schemeActionAttractingMap_comp_zero, Category.assoc, schemeActionFixedMap_comp,
    ← Category.assoc, schemeActionAttractingLimit_comp]

end GmCoordinateAction

end Langlands.GroupScheme
