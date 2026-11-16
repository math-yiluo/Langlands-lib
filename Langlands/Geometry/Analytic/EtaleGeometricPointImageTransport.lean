import Langlands.Geometry.Analytic.EtaleGeometricPointGeometry

/-! # Transport of prescribed field-point image lifting -/

noncomputable section

universe u v uL uC vC uF

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

/-- Image lifting relative to a natural transformation is invariant under
isomorphisms in the arrow category. -/
private theorem image_lift_of_arrow_iso
    {C : Type uC} [Category.{vC} C]
    (F G : C ⥤ Type uF) (η : F ⟶ G)
    {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y}
    (e : Arrow.mk f ≅ Arrow.mk g)
    (hf : ∀ p : F.obj B, η.app B p ∈ Set.range (G.map f) →
      ∃ q : F.obj A, F.map f q = p) :
    ∀ p : F.obj Y, η.app Y p ∈ Set.range (G.map g) →
      ∃ q : F.obj X, F.map g q = p := by
  rintro p ⟨x, hx⟩
  have hi : e.inv.left ≫ f = g ≫ e.inv.right := e.inv.w
  have hh : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  have hir : e.inv.right ≫ e.hom.right = 𝟙 Y := Arrow.inv_hom_id_right e
  have hp : η.app B (F.map e.inv.right p) ∈ Set.range (G.map f) := by
    refine ⟨G.map e.inv.left x, ?_⟩
    rw [← G.map_comp_apply, hi, G.map_comp_apply, hx]
    exact (congrArg (fun φ : F.obj Y ⟶ G.obj B => φ p)
      (η.naturality e.inv.right)).symm
  obtain ⟨q, hq⟩ := hf (F.map e.inv.right p) hp
  refine ⟨F.map e.hom.left q, ?_⟩
  rw [← F.map_comp_apply, hh, F.map_comp_apply, hq,
    ← F.map_comp_apply, hir]
  exact F.map_id_apply Y p

/-- The strong-map geometric input: lift the entire prescribed field point
whenever its ordinary point lies in the image of an all-pieces étale map. -/
def StrongEtaleFieldPointImageLiftStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (A B : AffinoidAtlasPresentation.{u, v, v} K)
    (g : ofSaturation A ⟶ ofSaturation B),
    AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := A) (B := B) g →
      ∀ p : AffinoidAtlasPresentation.FieldPoint L B.saturatedPresentation,
        p.point ∈ Set.range g.baseMap →
          ∃ q : AffinoidAtlasPresentation.FieldPoint L A.saturatedPresentation,
            q.map g A.atlas.saturatedAtlas_hasAllLocalDomains = p

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  [NormedAlgebra K L]

/-- The strong image-lifting input transports through the arrow isomorphism
in the definition of a localized étale morphism. -/
theorem exists_localized_fieldPoint_lift_of_strong
    (h : StrongEtaleFieldPointImageLiftStatement.{u, v, uL})
    {X Y : LocalizedCategory.{u, v, v} (K := K)} (f : X ⟶ Y) (hf : etale f)
    (p : (localizedFieldPointFunctor L).obj Y)
    (hp : ((localizedFieldPointProjection L).app Y p).down ∈
      Set.range (localizedSpaceFunctor.map f)) :
    ∃ q : (localizedFieldPointFunctor L).obj X,
      (localizedFieldPointFunctor L).map f q = p := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let G : LocalizedCategory.{u, v, v} (K := K) ⥤ Type (max u v uL) :=
    localizedSpaceFunctor ⋙ forget TopCat ⋙ uliftFunctor.{max u v uL, v}
  have hstrong :
      ∀ p : (localizedFieldPointFunctor L).obj (localizationFunctor.obj (ofSaturation B)),
        (localizedFieldPointProjection L).app _ p ∈
            Set.range (G.map (localizationFunctor.map g)) →
          ∃ q : (localizedFieldPointFunctor L).obj
              (localizationFunctor.obj (ofSaturation A)),
            (localizedFieldPointFunctor L).map (localizationFunctor.map g) q = p := by
    intro p hp
    obtain ⟨x, hx⟩ := hp
    have hx' : g.baseMap x.down = p.point := by
      have hx' := congrArg ULift.down hx
      change localizedSpaceFunctor.map (localizationFunctor.map g) x.down = p.point at hx'
      rw [localizedSpaceFunctor_map] at hx'
      change g.baseMap x.down = p.point at hx'
      exact hx'
    obtain ⟨q, hq⟩ := h K L A B g hg p ⟨x.down, hx'⟩
    refine ⟨q, ?_⟩
    change (fieldPointFunctor L).map g q = p
    exact hq
  apply image_lift_of_arrow_iso (localizedFieldPointFunctor L) G
    (localizedFieldPointProjection L) e hstrong p
  obtain ⟨x, hx⟩ := hp
  exact ⟨ULift.up x, ULift.ext _ _ hx⟩

namespace EtaleSite

/-- Strong image lifting and right cancellation for localized étale maps
give the prescribed field-point lift for every actual site arrow. -/
theorem geometricPointImageLift_of_strong
    (h : StrongEtaleFieldPointImageLiftStatement.{u, v, uL})
    (hcancel : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      MorphismProperty.HasOfPostcompProperty
        (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))
        (etale (K := K))) :
    GeometricPointImageLiftStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X U V f p hp
  have := hcancel K
  have hf : etale f.left := by
    apply (etale (K := K)).of_postcomp f.left U.hom U.prop
    simpa only [MorphismProperty.Over.w] using V.prop
  exact exists_localized_fieldPoint_lift_of_strong L h f.left hf p hp

end EtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
