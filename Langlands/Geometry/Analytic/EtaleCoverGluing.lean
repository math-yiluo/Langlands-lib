import Langlands.Geometry.Analytic.EtaleSite

/-! # Gluing analytic morphisms along jointly surjective étale families

Consequences of the sheaf property of the presheaf `U ↦ (U ⟶ T)` on the small étale site of
an analytic space `S`: morphisms out of `S` are determined by their restrictions to a jointly
surjective family of étale maps, and families of morphisms that agree on every pair of
factorizations glue.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The Hom presheaf `U ↦ (U.left ⟶ T)` on the small étale site of `S`. -/
abbrev etaleHomPresheaf (S T : LocalizedCategory.{u, v, v} (K := K)) :=
  (MorphismProperty.Over.forget (etale (K := K)) ⊤ S ⋙ Over.forget S).op ⋙ yoneda.obj T

/-- The terminal object `𝟙 S` of the small étale site of `S`. -/
abbrev etaleSiteTop (S : LocalizedCategory.{u, v, v} (K := K)) : EtaleSite S :=
  MorphismProperty.Over.mk ⊤ (𝟙 S) (etale_of_isIso _)

/-- Morphisms out of `S` agreeing on a jointly surjective étale family are equal. -/
theorem hom_ext_of_etale_cover {S T : LocalizedCategory.{u, v, v} (K := K)}
    (hS : Presieve.IsSheaf (etaleTopology S) (etaleHomPresheaf S T))
    {J : Type w} (U : J → LocalizedCategory.{u, v, v} (K := K)) (e : ∀ j, U j ⟶ S)
    (he : ∀ j, etale (e j))
    (hcov : ∀ s : localizedSpaceFunctor.obj S,
      ∃ j, s ∈ Set.range (localizedSpaceFunctor.map (e j)))
    (f g : S ⟶ T) (h : ∀ j, e j ≫ f = e j ≫ g) : f = g := by
  let R : Sieve (etaleSiteTop S) :=
    { arrows := fun _ a => a.left ≫ f = a.left ≫ g
      downward_closed := by
        intro V W a ha b
        change (b.left ≫ a.left) ≫ f = (b.left ≫ a.left) ≫ g
        exact (Category.assoc b.left a.left f).trans
          ((congrArg (fun k => b.left ≫ k) ha).trans (Category.assoc b.left a.left g).symm) }
  have hR : R ∈ etaleTopology S (etaleSiteTop S) := by
    apply mem_etaleTopology_of_jointlySurjective
    intro s
    obtain ⟨j, hj⟩ := hcov s
    let V : EtaleSite S := MorphismProperty.Over.mk ⊤ (e j) (he j)
    let a : V ⟶ etaleSiteTop S := MorphismProperty.Over.homMk (e j) (Category.comp_id _)
    exact ⟨V, a, h j, hj⟩
  exact (hS R hR).isSeparatedFor.ext (fun _ _ ha => ha)

/-- Morphisms on a jointly surjective étale family that agree on all pairs of
factorizations through the family glue to a morphism out of `S`. -/
theorem exists_glue_of_etale_cover {S T : LocalizedCategory.{u, v, v} (K := K)}
    (hS : Presieve.IsSheaf (etaleTopology S) (etaleHomPresheaf S T))
    {J : Type w} (U : J → LocalizedCategory.{u, v, v} (K := K)) (e : ∀ j, U j ⟶ S)
    (he : ∀ j, etale (e j))
    (hcov : ∀ s : localizedSpaceFunctor.obj S,
      ∃ j, s ∈ Set.range (localizedSpaceFunctor.map (e j)))
    (h : ∀ j, U j ⟶ T)
    (hcompat : ∀ (V : LocalizedCategory.{u, v, v} (K := K)) (j k : J)
      (a : V ⟶ U j) (b : V ⟶ U k), a ≫ e j = b ≫ e k → a ≫ h j = b ≫ h k) :
    ∃ g : S ⟶ T, ∀ j, e j ≫ g = h j := by
  classical
  let R : Sieve (etaleSiteTop S) :=
    { arrows := fun V _ => ∃ (j : J) (a : V.left ⟶ U j), a ≫ e j = V.hom
      downward_closed := by
        intro V W c hc b
        obtain ⟨j, a, ha⟩ := hc
        refine ⟨j, b.left ≫ a, ?_⟩
        rw [Category.assoc, ha]
        exact MorphismProperty.Over.w b }
  have hR : R ∈ etaleTopology S (etaleSiteTop S) := by
    apply mem_etaleTopology_of_jointlySurjective
    intro s
    obtain ⟨j, hj⟩ := hcov s
    let V : EtaleSite S := MorphismProperty.Over.mk ⊤ (e j) (he j)
    let a : V ⟶ etaleSiteTop S := MorphismProperty.Over.homMk (e j) (Category.comp_id _)
    exact ⟨V, a, ⟨j, 𝟙 _, Category.id_comp _⟩, hj⟩
  let x : Presieve.FamilyOfElements (etaleHomPresheaf S T) R.arrows :=
    fun _ _ hc => (Classical.choose_spec hc).choose ≫ h (Classical.choose hc)
  have hx_spec {V : EtaleSite S} (c : V ⟶ etaleSiteTop S) (hc : R c) :
      (Classical.choose_spec hc).choose ≫ e (Classical.choose hc) = V.hom :=
    (Classical.choose_spec hc).choose_spec
  have hx : x.Compatible := by
    intro V₁ V₂ W g₁ g₂ c₁ c₂ hc₁ hc₂ hw
    change g₁.left ≫ ((Classical.choose_spec hc₁).choose ≫ h (Classical.choose hc₁)) =
      g₂.left ≫ ((Classical.choose_spec hc₂).choose ≫ h (Classical.choose hc₂))
    rw [← Category.assoc, ← Category.assoc]
    apply hcompat
    rw [Category.assoc, Category.assoc, hx_spec, hx_spec, MorphismProperty.Over.w,
      MorphismProperty.Over.w]
  let g : S ⟶ T := (hS R hR).amalgamate x hx
  refine ⟨g, fun j => ?_⟩
  let V : EtaleSite S := MorphismProperty.Over.mk ⊤ (e j) (he j)
  let a : V ⟶ etaleSiteTop S := MorphismProperty.Over.homMk (e j) (Category.comp_id _)
  have ha : R a := ⟨j, 𝟙 _, Category.id_comp _⟩
  have hglue : a.left ≫ g = x a ha := (hS R hR).valid_glue hx a ha
  change e j ≫ g = h j
  refine hglue.trans ?_
  change (Classical.choose_spec ha).choose ≫ h (Classical.choose ha) = h j
  rw [← Category.id_comp (h j)]
  apply hcompat
  rw [hx_spec]
  exact (Category.id_comp _).symm

end Langlands.Analytic.SaturatedAtlasPresentation
