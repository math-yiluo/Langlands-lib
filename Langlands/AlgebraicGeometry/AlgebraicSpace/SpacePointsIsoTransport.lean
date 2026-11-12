import Langlands.AlgebraicGeometry.AlgebraicSpace.PointTopologyIso
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Mathlib.Topology.Connected.Basic

/-! # Transport of fibre predicates through presheaf isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Points

variable {F G : Presheaf S}

/-- Closedness of a point map transports through a presheaf isomorphism of its source. -/
theorem isClosedMap_of_iso {H : Presheaf S} (e : F ≅ G) (p : F ⟶ H) (q : G ⟶ H)
    (w : e.hom ≫ q = p)
    (hp : @IsClosedMap _ _ (pointTopology F) (pointTopology H) (map p)) :
    @IsClosedMap _ _ (pointTopology G) (pointTopology H) (map q) := by
  let : TopologicalSpace (Points F) := pointTopology F
  let : TopologicalSpace (Points G) := pointTopology G
  let : TopologicalSpace (Points H) := pointTopology H
  have hq : q = e.inv ≫ p := by rw [← w, Iso.inv_hom_id_assoc]
  have hm : map q = map p ∘ (isoHomeomorph e).symm := by
    funext x
    rw [hq, map_comp]
    rfl
  rw [hm]
  exact hp.comp (isoHomeomorph e).symm.isClosedMap

end Points

/-- The fibre pullbacks of isomorphic arrows agree over the same scheme test,
with its target point transported by the inverse target isomorphism. -/
def fibrePullbackIsoOfArrowIso
    {F G F' G' : Presheaf S} (f : F ⟶ G) (f' : F' ⟶ G')
    (eF : F ≅ F') (eG : G ≅ G') (w : eF.hom ≫ f' = f ≫ eG.hom)
    {A : Presheaf S} (y : A ⟶ G') :
    Limits.pullback f (y ≫ eG.inv) ≅ Limits.pullback f' y :=
  asIso (pullback.map f (y ≫ eG.inv) f' y eF.hom (𝟙 A) eG.hom w.symm (by simp))

/-- The fibre comparison keeps its projection to the test presheaf. -/
theorem fibrePullbackIsoOfArrowIso_hom_snd
    {F G F' G' : Presheaf S} (f : F ⟶ G) (f' : F' ⟶ G')
    (eF : F ≅ F') (eG : G ≅ G') (w : eF.hom ≫ f' = f ≫ eG.hom)
    {A : Presheaf S} (y : A ⟶ G') :
    (fibrePullbackIsoOfArrowIso f f' eF eG w y).hom ≫ pullback.snd f' y =
      pullback.snd f (y ≫ eG.inv) := by
  simp only [fibrePullbackIsoOfArrowIso, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Geometrically connected fibres are invariant under isomorphism of arrows. -/
theorem HasGeometricallyConnectedFibres.of_arrow_iso
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : HasGeometricallyConnectedFibres f) : HasGeometricallyConnectedFibres f' := by
  intro K _ s y
  let e := fibrePullbackIsoOfArrowIso (hom f) (hom f')
    ((forgetToPresheaf S).mapIso eX) ((forgetToPresheaf S).mapIso eY)
    ((forgetToPresheaf S).congr_map w) y
  let : TopologicalSpace
      (Points (Limits.pullback (hom f) (y ≫ ((forgetToPresheaf S).mapIso eY).inv))) :=
    pointTopology _
  let : TopologicalSpace (Points (Limits.pullback (hom f') y)) := pointTopology _
  exact (Points.isoHomeomorph e).connectedSpace_iff.mp
    (hf K s (y ≫ hom eY.inv))

/-- Quasi-compactness, defined by compact étale atlases of scheme pullbacks,
is invariant under an isomorphism of arrows. -/
theorem IsQuasiCompactMorphism.of_arrow_iso
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : IsQuasiCompactMorphism f) : IsQuasiCompactMorphism f' := by
  intro T hT y
  let e := fibrePullbackIsoOfArrowIso (hom f) (hom f')
    ((forgetToPresheaf S).mapIso eX) ((forgetToPresheaf S).mapIso eY)
    ((forgetToPresheaf S).congr_map w) y
  obtain ⟨U, a, hU, ha, hs⟩ := hf T hT (y ≫ hom eY.inv)
  exact ⟨U, a ≫ e.hom, hU, ha.comp_iso e, hs.comp_iso e⟩

/-- Universal closedness is invariant under an isomorphism of arrows. -/
theorem IsUniversallyClosedMorphism.of_arrow_iso
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : IsUniversallyClosedMorphism f) : IsUniversallyClosedMorphism f' := by
  intro T y
  let e := fibrePullbackIsoOfArrowIso (hom f) (hom f')
    ((forgetToPresheaf S).mapIso eX) ((forgetToPresheaf S).mapIso eY)
    ((forgetToPresheaf S).congr_map w) y
  exact Points.isClosedMap_of_iso e _ _
    (fibrePullbackIsoOfArrowIso_hom_snd _ _ _ _ _ y)
    (hf T (y ≫ hom eY.inv))

end Langlands.AlgebraicGeometry.AlgebraicSpace
