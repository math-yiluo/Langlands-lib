import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismPointMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePointsIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedStructuralFibres
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Universal closedness reflected through a surjective source cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {S : Scheme.{u}}

/-- The actual map from the fibre of a composite to the fibre after the source map. -/
def sourceCoverFibreMap {A F G H : Presheaf S} (a : A ⟶ F) (f : F ⟶ G) (y : H ⟶ G) :
    Limits.pullback (a ≫ f) y ⟶ Limits.pullback f y :=
  pullback.map _ _ _ _ a (𝟙 H) (𝟙 G) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem sourceCoverFibreMap_snd {A F G H : Presheaf S}
    (a : A ⟶ F) (f : F ⟶ G) (y : H ⟶ G) :
    sourceCoverFibreMap a f y ≫ pullback.snd f y = pullback.snd (a ≫ f) y := by
  simp [sourceCoverFibreMap, pullback.map]

/-- The fibre comparison is the base change of the source map. -/
theorem sourceCoverFibreMap_isPullback {A F G H : Presheaf S}
    (a : A ⟶ F) (f : F ⟶ G) (y : H ⟶ G) :
    IsPullback (pullback.fst (a ≫ f) y) (sourceCoverFibreMap a f y)
      a (pullback.fst f y) := by
  have ho : IsPullback (pullback.fst (a ≫ f) y)
      (sourceCoverFibreMap a f y ≫ pullback.snd f y) (a ≫ f) y := by
    simpa only [sourceCoverFibreMap_snd] using IsPullback.of_hasPullback (a ≫ f) y
  apply ho.of_bot _ (IsPullback.of_hasPullback f y)
  simp [sourceCoverFibreMap, pullback.map]

/-- Geometric surjectivity is preserved in the actual fibre comparison. -/
theorem sourceCoverFibreMap_isSurjective {A F G H : Presheaf S}
    {a : A ⟶ F} (ha : IsSurjective a) (f : F ⟶ G) (y : H ⟶ G) :
    IsSurjective (sourceCoverFibreMap a f y) := by
  have : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
      (schemeYoneda S)) (sourceCoverFibreMap_isPullback a f y) ha

/-- A represented scheme map is closed on presheaf points when it is closed on schemes. -/
theorem isClosedMap_points_schemeYoneda {U V : Over S} (q : U ⟶ V)
    (hq : IsClosedMap q.left) :
    @IsClosedMap _ _ (pointTopology ((schemeYoneda S).obj U))
      (pointTopology ((schemeYoneda S).obj V)) (Points.map ((schemeYoneda S).map q)) := by
  let := pointTopology ((schemeYoneda S).obj U)
  let := pointTopology ((schemeYoneda S).obj V)
  let eU := schemePointsHomeomorph U
  let eV := schemePointsHomeomorph V
  have h : IsClosedMap (eV.symm ∘ q.left ∘ eU) :=
    eV.symm.isClosedMap.comp (hq.comp eU.isClosedMap)
  have he : eV.symm ∘ q.left ∘ eU = Points.map ((schemeYoneda S).map q) := by
    funext x
    apply eV.injective
    rw [Function.comp_apply, Function.comp_apply, eV.apply_symm_apply]
    exact (schemePointsTo_map q x).symm
  rwa [he] at h

/-- A representable relative universally closed map satisfies the point-topology definition. -/
theorem isUniversallyClosedMorphism_of_relative
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (MorphismProperty.inverseImage (@UniversallyClosed.{u})
      (Over.forget S)).relative (schemeYoneda S) (hom f)) :
    IsUniversallyClosedMorphism f := by
  intro T y
  let hr := hf.1
  have hp : UniversallyClosed (hr.snd y).left :=
    hf.2 y (hr.fst y) (hr.snd y) (hr.isPullback y)
  let := hp
  exact Points.isClosedMap_of_iso (hr.isPullback y).isoPullback
    ((schemeYoneda S).map (hr.snd y)) (pullback.snd (hom f) y)
    (hr.isPullback y).isoPullback_hom_snd
    (isClosedMap_points_schemeYoneda (hr.snd y) (hr.snd y).left.isClosedMap)

/-- Scheme universal closedness gives the published algebraic-space predicate. -/
theorem isUniversallyClosedMorphism_schemeToSpace {U V : Over S}
    (q : U ⟶ V) (hq : UniversallyClosed q.left) :
    IsUniversallyClosedMorphism ((schemeToSpace S).map q) := by
  have : (MorphismProperty.inverseImage (@UniversallyClosed.{u})
      (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  apply isUniversallyClosedMorphism_of_relative
  exact MorphismProperty.relative_map
    (P := MorphismProperty.inverseImage (@UniversallyClosed.{u}) (Over.forget S)) hq

/-- Universal closedness of a composite reflects through a represented surjective source map. -/
theorem IsUniversallyClosedMorphism.of_surjective_comp
    {W X Y : AlgebraicSpace S} (a : W ⟶ X) (f : X ⟶ Y)
    (ha : IsSurjective (hom a)) (hf : IsUniversallyClosedMorphism (a ≫ f)) :
    IsUniversallyClosedMorphism f := by
  change ∀ T y, @IsClosedMap _ _
    (pointTopology (Limits.pullback (hom f) y)) (pointTopology ((schemeYoneda S).obj T)) _
  change ∀ T y, @IsClosedMap _ _
    (pointTopology (Limits.pullback (hom a ≫ hom f) y))
    (pointTopology ((schemeYoneda S).obj T)) _ at hf
  intro T y
  let m := sourceCoverFibreMap (hom a) (hom f) y
  let := pointTopology (Limits.pullback (hom a ≫ hom f) y)
  let := pointTopology (Limits.pullback (hom f) y)
  let := pointTopology ((schemeYoneda S).obj T)
  let g : (schemeToSpace S).obj T ⟶ Y := homMk y
  obtain ⟨V, b, hbe, hbs⟩ := (fibreProduct f g).property.2
  let e := FibreProduct.presheafIso f g
  have hm : Continuous (Points.map m) :=
    Points.continuous_map_of_atlas m (b ≫ e.hom) (hbe.comp_iso e) (hbs.comp_iso e)
  have hs : Function.Surjective (Points.map m) :=
    Points.surjective_map (sourceCoverFibreMap_isSurjective ha (hom f) y)
  have he : Points.map (pullback.snd (hom a ≫ hom f) y) =
      Points.map (pullback.snd (hom f) y) ∘ Points.map m := by
    funext x
    change Points.map (pullback.snd (hom a ≫ hom f) y) x =
      Points.map (pullback.snd (hom f) y)
        (Points.map (sourceCoverFibreMap (hom a) (hom f) y) x)
    rw [← Points.map_comp, sourceCoverFibreMap_snd]
  intro C hC
  have h := hf T y _ (hC.preimage hm)
  change IsClosed (Points.map (pullback.snd (hom a ≫ hom f) y) ''
    (Points.map m ⁻¹' C)) at h
  rw [he, Set.image_comp, Set.image_preimage_eq C hs] at h
  exact h

/-- A surjective scheme cover with universally closed structural map detects
universal closedness of the space over its base. -/
theorem isUniversallyClosed_structural_of_scheme_cover
    (X : AlgebraicSpace S) (U : Over S)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsSurjective a) (hU : UniversallyClosed U.hom) :
    IsUniversallyClosedMorphism (structuralMorphism X) := by
  let a' : (schemeToSpace S).obj U ⟶ X := homMk a
  let q : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom (by simp)
  have hq : IsUniversallyClosedMorphism ((schemeToSpace S).map q) :=
    isUniversallyClosedMorphism_schemeToSpace q hU
  have he : a' ≫ structuralMorphism X = (schemeToSpace S).map q := by
    apply (homEquiv _ _).injective
    exact (basePresheafIsTerminal S).hom_ext _ _
  apply IsUniversallyClosedMorphism.of_surjective_comp a' (structuralMorphism X) ha
  rwa [he]

end Langlands.AlgebraicGeometry.AlgebraicSpace
