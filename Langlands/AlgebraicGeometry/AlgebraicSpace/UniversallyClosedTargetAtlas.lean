import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePointsIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismPointMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasComponentIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedFibreTargetAtlas

/-! # Universal closedness tested on a surjective etale target atlas -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology IsLocalRing

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Points

/-- Any compatible pair of quotient points lifts to the actual presheaf pullback. -/
theorem exists_pullback_point {F G H : Presheaf S} (f : F ⟶ H) (g : G ⟶ H)
    (x : Points F) (y : Points G) (h : map f x = map g y) :
    ∃ z : Points (Limits.pullback f g),
      map (pullback.fst f g) z = x ∧ map (pullback.snd f g) z = y := by
  induction x using Quot.ind with
  | _ p =>
    induction y using Quot.ind with
    | _ q =>
      let a : (schemeYoneda S).obj (Over.mk p.base) ⟶ F :=
        uliftYonedaEquiv.{u + 1}.symm p.val
      let b : (schemeYoneda S).obj (Over.mk q.base) ⟶ G :=
        uliftYonedaEquiv.{u + 1}.symm q.val
      have he : chartPointMap (a ≫ f) (closedPoint p.field) =
          chartPointMap (b ≫ g) (closedPoint q.field) := by
        change map (a ≫ f) (schemePoint _ _) = map (b ≫ g) (schemePoint _ _)
        rw [map_comp, map_comp]
        change map f (chartPointMap a _) = map g (chartPointMap b _)
        rw [chartPointMap_fieldPoint p, chartPointMap_fieldPoint q]
        exact h
      obtain ⟨T, r, s, t, hw, hr, hs⟩ :=
        (chartPointMap_eq_iff_sameImage₂ _ _ _ _).mp he
      let l : (schemeYoneda S).obj T ⟶ Limits.pullback f g :=
        pullback.lift ((schemeYoneda S).map r ≫ a)
          ((schemeYoneda S).map s ≫ b) (by simpa only [Category.assoc] using hw)
      refine ⟨chartPointMap l t, ?_, ?_⟩
      · change map (pullback.fst f g) (map l (schemePoint T t)) = Quot.mk _ p
        rw [← map_comp, pullback.lift_fst]
        change chartPointMap ((schemeYoneda S).map r ≫ a) t = _
        rw [chartPointMap_comp, hr]
        exact chartPointMap_fieldPoint p
      · change map (pullback.snd f g) (map l (schemePoint T t)) = Quot.mk _ q
        rw [← map_comp, pullback.lift_snd]
        change chartPointMap ((schemeYoneda S).map s ≫ b) t = _
        rw [chartPointMap_comp, hs]
        exact chartPointMap_fieldPoint q

/-- The point lifting property holds for every actual cartesian presheaf square. -/
theorem exists_point_of_isPullback {P F G H : Presheaf S}
    {a : P ⟶ F} {b : P ⟶ G} {f : F ⟶ H} {g : G ⟶ H}
    (hp : IsPullback a b f g) (x : Points F) (y : Points G)
    (h : map f x = map g y) :
    ∃ z : Points P, map a z = x ∧ map b z = y := by
  obtain ⟨z, hx, hy⟩ := exists_pullback_point f g x y h
  have ha : hp.isoPullback.inv ≫ a = pullback.fst f g := by
    exact (Iso.inv_comp_eq hp.isoPullback).mpr hp.isoPullback_hom_fst.symm
  have hb : hp.isoPullback.inv ≫ b = pullback.snd f g := by
    exact (Iso.inv_comp_eq hp.isoPullback).mpr hp.isoPullback_hom_snd.symm
  refine ⟨map hp.isoPullback.inv z, ?_, ?_⟩
  · rw [← map_comp, ha, hx]
  · rw [← map_comp, hb, hy]

/-- In a cartesian presheaf square, images commute with inverse image on quotient points. -/
theorem preimage_image_of_isPullback {P F G H : Presheaf S}
    {a : P ⟶ F} {b : P ⟶ G} {f : F ⟶ H} {g : G ⟶ H}
    (hp : IsPullback a b f g) (C : Set (Points F)) :
    map g ⁻¹' (map f '' C) = map b '' (map a ⁻¹' C) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hz₁, hz₂⟩ := exists_point_of_isPullback hp x y hxy
    refine ⟨z, ?_, hz₂⟩
    change map a z ∈ C
    rwa [hz₁]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨map a z, hz, ?_⟩
    rw [← map_comp, hp.w, map_comp]

end Points

/-- Compare the test of a target pullback with the original test fibre. -/
def targetCoverFibreMap {P F V T G R : Presheaf S}
    {a : P ⟶ F} {p : P ⟶ V} {f : F ⟶ G} {b : V ⟶ G}
    (h : IsPullback a p f b) {r : R ⟶ V} {q : R ⟶ T} {y : T ⟶ G}
    (hR : IsPullback r q b y) : Limits.pullback p r ⟶ Limits.pullback f y :=
  pullback.lift (pullback.fst p r ≫ a) (pullback.snd p r ≫ q) (by
    rw [Category.assoc, h.w, ← Category.assoc, pullback.condition,
      Category.assoc, hR.w, Category.assoc])

/-- The target-cover comparison is itself cartesian over the test cover. -/
theorem targetCoverFibreMap_isPullback {P F V T G R : Presheaf S}
    {a : P ⟶ F} {p : P ⟶ V} {f : F ⟶ G} {b : V ⟶ G}
    (h : IsPullback a p f b) {r : R ⟶ V} {q : R ⟶ T} {y : T ⟶ G}
    (hR : IsPullback r q b y) :
    IsPullback (targetCoverFibreMap h hR) (pullback.snd p r)
      (pullback.snd f y) q := by
  have ho := (IsPullback.of_hasPullback p r).paste_horiz h
  rw [hR.w] at ho
  have ho' : IsPullback
      (targetCoverFibreMap h hR ≫ pullback.fst f y) (pullback.snd p r)
      f (q ≫ y) := by
    simpa only [targetCoverFibreMap, pullback.lift_fst] using ho
  apply ho'.of_right _ (IsPullback.of_hasPullback f y)
  simp only [targetCoverFibreMap, pullback.lift_snd]

/-- Universal closedness is preserved in an actual cartesian space square. -/
theorem IsUniversallyClosedMorphism.of_isPullback
    {X' Y' X Y : AlgebraicSpace S} {a : X' ⟶ X} {p : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y}
    (h : IsPullback (hom a) (hom p) (hom f) (hom b))
    (hf : IsUniversallyClosedMorphism f) : IsUniversallyClosedMorphism p := by
  intro T y
  let e := iteratedFibrePullbackIso h y
  have he : e.hom ≫ pullback.snd (hom f) (y ≫ hom b) = pullback.snd (hom p) y :=
    (IsPullback.of_hasPullback (hom p) y).paste_horiz h |>.isoPullback_hom_snd
  apply Points.isClosedMap_of_iso e.symm _ _ _ (hf T (y ≫ hom b))
  change e.inv ≫ pullback.snd (hom p) y = _
  rw [← he, Iso.inv_hom_id_assoc]

/-- An actual surjective etale target atlas tests universal closedness. -/
theorem isUniversallyClosedMorphism_iff_targetAtlas {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)
    (hb : IsEtale b) (hs : IsSurjective b) :
    IsUniversallyClosedMorphism f ↔
      IsUniversallyClosedMorphism
        (FibreProduct.snd f (homMk b : (schemeToSpace S).obj V ⟶ Y)) := by
  let b₀ : (schemeToSpace S).obj V ⟶ Y := homMk b
  let p := FibreProduct.snd f b₀
  let h := FibreProduct.isPullback_presheaf f b₀
  constructor
  · exact IsUniversallyClosedMorphism.of_isPullback h
  · intro hp T y
    let hr := hb.representable
    let r := hr.fst' y
    let q := hr.snd y
    have hqE : Etale q.left := hb.projection y (hr.fst y) q (hr.isPullback y)
    have hqS : Surjective q.left := hs.projection y (hr.fst y) q (hr.isPullback y)
    let m := targetCoverFibreMap h (hr.isPullback' y)
    let := pointTopology (Limits.pullback (hom p) ((schemeYoneda S).map r))
    let := pointTopology (Limits.pullback (hom f) y)
    let := pointTopology ((schemeYoneda S).obj T)
    let := pointTopology ((schemeYoneda S).obj (hr.pullback y))
    let y₀ : (schemeToSpace S).obj T ⟶ Y := homMk y
    obtain ⟨A, c, hce, hcs⟩ := (fibreProduct f y₀).property.2
    let e := FibreProduct.presheafIso f y₀
    have hm : Continuous (Points.map m) :=
      Points.continuous_map_of_atlas m (c ≫ e.hom) (hce.comp_iso e) (hcs.comp_iso e)
    have hq : @IsQuotientMap (hr.pullback y).left (Points ((schemeYoneda S).obj T))
        _ (pointTopology _) (chartPointMap ((schemeYoneda S).map q)) :=
      isQuotientMap_chartPointMap _ (isEtale_map q hqE)
        (MorphismProperty.relative_map
          (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hqS)
    intro C hC
    have hc := hp (hr.pullback y) ((schemeYoneda S).map r) _ (hC.preimage hm)
    have he := Points.preimage_image_of_isPullback
      (targetCoverFibreMap_isPullback h (hr.isPullback' y)) C
    change Points.map ((schemeYoneda S).map q) ⁻¹'
      (Points.map (pullback.snd (hom f) y) '' C) =
        Points.map (pullback.snd (hom p) ((schemeYoneda S).map r)) ''
          (Points.map m ⁻¹' C) at he
    rw [← he] at hc
    apply hq.isClosed_preimage.mp
    exact hc.preimage (continuous_schemePoint (hr.pullback y))

end Langlands.AlgebraicGeometry.AlgebraicSpace
