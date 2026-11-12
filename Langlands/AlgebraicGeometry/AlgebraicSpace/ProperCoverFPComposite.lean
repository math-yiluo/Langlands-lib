import Langlands.AlgebraicGeometry.AlgebraicSpace.UniversallyClosedSourceCover
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniversallyClosedTargetAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemePointsTopology

/-! # Universal closedness of a scheme mapping to a universally closed space -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Points

/-- A presheaf map is closed on points when its fibres over a surjective étale atlas of the
target are closed on points, provided the source also has a surjective étale atlas. -/
theorem isClosedMap_of_atlas_fibres {F G : Presheaf S} (m : F ⟶ G)
    {W : Over S} (c : (schemeYoneda S).obj W ⟶ F) (hce : IsEtale c) (hcs : IsSurjective c)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ G) (hbe : IsEtale b) (hbs : IsSurjective b)
    (hm : @IsClosedMap _ _ (pointTopology (Limits.pullback m b))
      (pointTopology ((schemeYoneda S).obj V)) (map (pullback.snd m b))) :
    @IsClosedMap _ _ (pointTopology F) (pointTopology G) (map m) := by
  let := pointTopology F
  let := pointTopology G
  let := pointTopology (Limits.pullback m b)
  let := pointTopology ((schemeYoneda S).obj V)
  have hfst : Continuous (map (pullback.fst m b)) := continuous_map_of_atlas _ c hce hcs
  have hq := isQuotientMap_chartPointMap b hbe hbs
  intro C hC
  have hc := hm _ (hC.preimage hfst)
  rw [← preimage_image_of_isPullback (IsPullback.of_hasPullback m b) C] at hc
  apply hq.isClosed_preimage.mp
  exact hc.preimage (continuous_schemePoint V)

end Points

/-- A universally closed morphism of algebraic spaces is closed on points. -/
theorem IsUniversallyClosedMorphism.isClosedMap_points {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (hf : IsUniversallyClosedMorphism f) :
    @IsClosedMap _ _ (pointTopology X.presheaf) (pointTopology Y.presheaf)
      (Points.map (hom f)) := by
  obtain ⟨V, b, hbe, hbs⟩ := Y.property.2
  obtain ⟨W, c, hce, hcs⟩ := X.property.2
  exact Points.isClosedMap_of_atlas_fibres (hom f) c hce hcs b hbe hbs (hf V b)

/-- Universally closed morphisms of algebraic spaces are stable under composition. -/
theorem IsUniversallyClosedMorphism.comp {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    {g : Y ⟶ Z} (hf : IsUniversallyClosedMorphism f) (hg : IsUniversallyClosedMorphism g) :
    IsUniversallyClosedMorphism (f ≫ g) := by
  change ∀ T y, @IsClosedMap _ _
    (pointTopology (Limits.pullback (hom f ≫ hom g) y))
    (pointTopology ((schemeYoneda S).obj T)) _
  intro T y
  let y₀ : (schemeToSpace S).obj T ⟶ Z := homMk y
  let m := sourceCoverFibreMap (hom f) (hom g) y
  let := pointTopology (Limits.pullback (hom f ≫ hom g) y)
  let := pointTopology (Limits.pullback (hom g) y)
  let := pointTopology ((schemeYoneda S).obj T)
  obtain ⟨W, c, hce, hcs⟩ := (fibreProduct (f ≫ g) y₀).property.2
  obtain ⟨V, b, hbe, hbs⟩ := (fibreProduct g y₀).property.2
  let eW := FibreProduct.presheafIso (f ≫ g) y₀
  let eV := FibreProduct.presheafIso g y₀
  have hpaste : IsPullback (pullback.fst m (b ≫ eV.hom) ≫ pullback.fst (hom f ≫ hom g) y)
      (pullback.snd m (b ≫ eV.hom)) (hom f) ((b ≫ eV.hom) ≫ pullback.fst (hom g) y) :=
    (IsPullback.of_hasPullback m (b ≫ eV.hom)).paste_horiz
      (sourceCoverFibreMap_isPullback (hom f) (hom g) y)
  have hfib : @IsClosedMap _ _ (pointTopology (Limits.pullback m (b ≫ eV.hom)))
      (pointTopology ((schemeYoneda S).obj V)) (Points.map (pullback.snd m (b ≫ eV.hom))) :=
    Points.isClosedMap_of_iso hpaste.isoPullback.symm _ _ hpaste.isoPullback_inv_snd
      (hf V ((b ≫ eV.hom) ≫ pullback.fst (hom g) y))
  have hm : IsClosedMap (Points.map m) :=
    Points.isClosedMap_of_atlas_fibres m (c ≫ eW.hom) (hce.comp_iso eW) (hcs.comp_iso eW)
      (b ≫ eV.hom) (hbe.comp_iso eV) (hbs.comp_iso eV) hfib
  have he : Points.map (pullback.snd (hom f ≫ hom g) y) =
      Points.map (pullback.snd (hom g) y) ∘ Points.map m := by
    funext x
    change Points.map (pullback.snd (hom f ≫ hom g) y) x =
      Points.map (pullback.snd (hom g) y) (Points.map m x)
    rw [← Points.map_comp, sourceCoverFibreMap_snd]
  change IsClosedMap (Points.map (pullback.snd (hom f ≫ hom g) y))
  rw [he]
  exact (hg T y).comp hm

/-- A morphism of schemes over `S` is universally closed when the induced morphism of
algebraic spaces is universally closed in the point-topology sense. -/
theorem universallyClosed_of_isUniversallyClosedMorphism_schemeToSpace {U V : Over S}
    (q : U ⟶ V) (hq : IsUniversallyClosedMorphism ((schemeToSpace S).map q)) :
    UniversallyClosed q.left := by
  rw [universallyClosed_iff]
  apply MorphismProperty.universally_mk'
  intro T' f' _
  let T : Over S := Over.mk (f' ≫ V.hom)
  let t : T ⟶ V := Over.homMk f' rfl
  let Y := schemeYoneda S
  let hr : Y.relativelyRepresentable (Y.map q) :=
    Functor.relativelyRepresentable.map Y q
  have hsq : IsPullback (hr.fst' (Y.map t)) (hr.snd (Y.map t)) q t :=
    hr.isPullback_of_map t
  have hsq' : IsPullback (hr.snd (Y.map t)).left (hr.fst' (Y.map t)).left f' q.left :=
    (hsq.map (Over.forget S)).flip
  -- closedness on presheaf points of the represented projection
  let := pointTopology (Limits.pullback (Y.map q) (Y.map t))
  let := pointTopology (Y.obj (hr.pullback (Y.map t)))
  let := pointTopology (Y.obj T)
  have h₀ : IsClosedMap (Points.map (pullback.snd (Y.map q) (Y.map t))) := hq T (Y.map t)
  have h₁ : IsClosedMap (Points.map (Y.map (hr.snd (Y.map t)))) :=
    Points.isClosedMap_of_iso (hr.isPullback (Y.map t)).isoPullback.symm _ _
      (hr.isPullback (Y.map t)).isoPullback_inv_snd h₀
  -- closedness on scheme points
  let eP := schemePointsHomeomorph (hr.pullback (Y.map t))
  let eT := schemePointsHomeomorph T
  have h₂ : IsClosedMap (hr.snd (Y.map t)).left := by
    have h := eT.isClosedMap.comp (h₁.comp eP.symm.isClosedMap)
    have he : eT ∘ Points.map (Y.map (hr.snd (Y.map t))) ∘ eP.symm =
        (hr.snd (Y.map t)).left := by
      funext x
      change schemePointsTo T (Points.map (Y.map (hr.snd (Y.map t)))
        (schemePoint _ x)) = _
      rw [schemePointsTo_map, schemePointsTo_schemePoint]
    rwa [he] at h
  change IsClosedMap (pullback.fst f' q.left)
  rw [← hsq'.isoPullback_hom_fst] at h₂
  have := (topologically_respectsIso (P := @IsClosedMap)
    (fun e ↦ e.isClosedMap) (fun _ _ hf hg ↦ hg.comp hf))
  exact (MorphismProperty.cancel_left_of_respectsIso (topologically @IsClosedMap)
    hsq'.isoPullback.hom (pullback.fst f' q.left)).mp h₂

/-- A scheme with a represented universally closed map to an algebraic space whose
structural morphism is universally closed is universally closed over the base. -/
theorem universallyClosed_of_relative_of_structural
    (X : AlgebraicSpace S) (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : (MorphismProperty.inverseImage (@UniversallyClosed.{u})
      (Over.forget S)).relative (schemeYoneda S) a)
    (hX : IsUniversallyClosedMorphism (structuralMorphism X)) :
    UniversallyClosed U.hom := by
  let a' : (schemeToSpace S).obj U ⟶ X := homMk a
  let q : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom (by simp)
  have ha' : IsUniversallyClosedMorphism a' := isUniversallyClosedMorphism_of_relative ha
  have he : a' ≫ structuralMorphism X = (schemeToSpace S).map q := by
    apply (homEquiv _ _).injective
    exact (basePresheafIsTerminal S).hom_ext _ _
  have hq : IsUniversallyClosedMorphism ((schemeToSpace S).map q) := by
    rw [← he]
    exact ha'.comp hX
  exact universallyClosed_of_isUniversallyClosedMorphism_schemeToSpace q hq

end Langlands.AlgebraicGeometry.AlgebraicSpace
