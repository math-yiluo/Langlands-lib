import Langlands.AlgebraicGeometry.SectionComponentDvrSpecialization
import Langlands.AlgebraicGeometry.SectionComponentBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.SectionComponent

/-- The section of the base-changed family induced by a point valued in an
arbitrary scheme. -/
def valuedPointSection {X Y T : Scheme.{u}} (f : X ⟶ Y) (a : T ⟶ X) :
    T ⟶ pullback f (a ≫ f) :=
  pullback.lift a (𝟙 _) (by simp)

@[reassoc (attr := simp)]
theorem valuedPointSection_fst {X Y T : Scheme.{u}} (f : X ⟶ Y) (a : T ⟶ X) :
    valuedPointSection f a ≫ pullback.fst f (a ≫ f) = a :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem valuedPointSection_snd {X Y T : Scheme.{u}} (f : X ⟶ Y) (a : T ⟶ X) :
    valuedPointSection f a ≫ pullback.snd f (a ≫ f) = 𝟙 _ :=
  pullback.lift_snd ..

/-- Geometric reducedness of the indexed selected component supplies reducedness
of the selected component after any actual base change. -/
theorem isReduced_fiberComponentOpen_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    {e : Y ⟶ X} {e' : Y' ⟶ X'} {he : e ≫ f = 𝟙 _} {he' : e' ≫ f' = 𝟙 _}
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    (hsection : e' ≫ g = b ≫ e) (y' : Y')
    [GeometricallyReduced
      ((fiberComponentOpen f e he (b y')).ι ≫ f.fiberToSpecResidueField (b y'))] :
    AlgebraicGeometry.IsReduced (fiberComponentOpen f' e' he' y') := by
  let C := fiberComponentOpen f e he (b y')
  let a := fiberMap g b h.w y'
  have hF := isPullback_fiberToSpecResidueField_of_isPullback h y'
  have hrect := (IsPullback.of_hasPullback C.ι a).flip.paste_horiz hF.flip
  have : AlgebraicGeometry.IsReduced (pullback C.ι a) :=
    GeometricallyReduced.geometrically_isReduced
      (f := C.ι ≫ f.fiberToSpecResidueField (b y')) _ _ _ hrect.flip
  exact isReduced_of_isOpenImmersion (fiberComponentBaseChangeIso h hsection y').hom

/-- A DVR-valued point through a selected geometrically reduced indexed fibre
component has its generic point in the original selected-component union. -/
theorem dvr_generic_mem_componentSet
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 _)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : Spec (CommRingCat.of R) ⟶ X)
    [GeometricallyReduced
      ((fiberComponentOpen f e he (f (a (IsLocalRing.closedPoint R)))).ι ≫
        f.fiberToSpecResidueField (f (a (IsLocalRing.closedPoint R))))]
    (hclosed : a (IsLocalRing.closedPoint R) ∈ componentSet f e he) :
    a (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ componentSet f e he := by
  let b := a ≫ f
  let q := pullback.snd f b
  let e' := baseChangeSection f e he b
  have he' : e' ≫ q = 𝟙 _ := baseChangeSection_snd f e he b
  let v := valuedPointSection f a
  have hv : v ≫ q = 𝟙 _ := valuedPointSection_snd f a
  have hvfst : v ≫ pullback.fst f b = a := valuedPointSection_fst f a
  have hset : pullback.fst f b ⁻¹' componentSet f e he = componentSet q e' he' :=
    preimage_componentSet_of_isPullback_locallyOfFiniteType
      (.of_hasPullback f b) (baseChangeSection_fst f e he b)
  let : GeometricallyReduced
      ((fiberComponentOpen f e he (b (IsLocalRing.closedPoint R))).ι ≫
        f.fiberToSpecResidueField (b (IsLocalRing.closedPoint R))) := by
    have hb : b (IsLocalRing.closedPoint R) = f (a (IsLocalRing.closedPoint R)) :=
      Scheme.Hom.comp_apply a f _
    rw [hb]
    infer_instance
  let : AlgebraicGeometry.IsReduced (fiberComponentOpen q e' he' (IsLocalRing.closedPoint R)) :=
    isReduced_fiberComponentOpen_of_isPullback (he := he) (he' := he') (.of_hasPullback f b)
      (baseChangeSection_fst f e he b) (IsLocalRing.closedPoint R)
  have hclosed' : v (IsLocalRing.closedPoint R) ∈ componentSet q e' he' := by
    rw [← hset]
    change pullback.fst f b (v (IsLocalRing.closedPoint R)) ∈ componentSet f e he
    rwa [← Scheme.Hom.comp_apply, hvfst]
  have hgeneric := section_generic_mem_componentSet_of_closed R q e' v he' hv hclosed'
  rw [← hset] at hgeneric
  change pullback.fst f b (v (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) ∈
    componentSet f e he at hgeneric
  rwa [← Scheme.Hom.comp_apply, hvfst] at hgeneric

end Langlands.AlgebraicGeometry.SectionComponent
