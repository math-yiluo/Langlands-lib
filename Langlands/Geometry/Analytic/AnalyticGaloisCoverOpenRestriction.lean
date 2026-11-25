import Langlands.Geometry.Analytic.AnalyticGaloisCover
import Langlands.Geometry.Analytic.ContinuousDomainEmbeddings
import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof

/-! # Open restriction of analytic Galois coverings -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.AnalyticGaloisCover

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}
  {Γ : Type z} [Group Γ] (c : AnalyticGaloisCover Γ p)
  (U : Opens (localizedSpaceFunctor.obj X))

local notation "D" => preimageOpenDomain p (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
local notation "ιY" => domainι Y D
local notation "ιX" =>
  domainι X (openDomain (presentationOf X) (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)
local notation "q" => preimageOpenDomainMap p (U : Set (localizedSpaceFunctor.obj X)) U.isOpen

private theorem isInvariant_preimageOpenDomain : IsInvariantDomain (analyticActionOfAut c.deck) D := by
  intro γ y hy
  change localizedSpaceFunctor.obj Y at y
  change localizedSpaceFunctor.map p (localizedSpaceFunctor.map (c.deck γ).asIso.hom y) ∈ U
  have h := congrArg (fun f : Y ⟶ X => localizedSpaceFunctor.map f y) (c.deck_over γ)
  simp only [Functor.map_comp, TopCat.comp_app] at h
  exact h.symm ▸ hy

private def restrictedDeck : Γ →* Aut (domainObj Y D) :=
  (invariantDomainAction (analyticActionOfAut c.deck) D (c.isInvariant_preimageOpenDomain U)).ρAut

@[reassoc]
private theorem restrictedDeck_hom_comp (γ : Γ) :
    (c.restrictedDeck U γ).asIso.hom ≫ ιY = ιY ≫ (c.deck γ).asIso.hom :=
  (invariantDomainInclusion _ _ (c.isInvariant_preimageOpenDomain U)).comm γ

private theorem restrictedDeck_over (γ : Γ) : (c.restrictedDeck U γ).asIso.hom ≫ q = q := by
  have h : q ≫ ιX = ιY ≫ p :=
    preimageOpenDomainMap_comp p (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  apply (cancel_mono ιX).mp
  rw [Category.assoc, h, c.restrictedDeck_hom_comp_assoc, c.deck_over]

/-- A Galois covering restricts to a Galois covering over every open domain of
its base, with the same deck group. -/
def restrictOpen : AnalyticGaloisCover Γ q := by
  let V : Set (localizedSpaceFunctor.obj Y) := localizedSpaceFunctor.map p ⁻¹' U
  have hV : IsOpen V := U.isOpen.preimage (localizedSpaceFunctor.map p).hom.continuous
  let E := preimageOpenDomain c.fst V hV
  let ιP := domainι c.relation E
  let r₁ : domainObj c.relation E ⟶ domainObj Y D := preimageOpenDomainMap c.fst V hV
  have h₁ : IsPullback r₁ ιP ιY c.fst := isPullback_preimageOpenDomain c.fst V hV
  let r₂ := domainRestrict E D c.snd (by
    intro t ht
    change localizedSpaceFunctor.obj c.relation at t
    change localizedSpaceFunctor.map p (localizedSpaceFunctor.map c.snd t) ∈ U
    rw [← TopCat.comp_app, ← Functor.map_comp, ← c.isPullback.w, Functor.map_comp, TopCat.comp_app]
    exact ht)
  have h₂ : r₂ ≫ ιY = ιP ≫ c.snd := domainRestrict_comp _ _ _ _
  have hq : IsPullback q ιY ιX p :=
    isPullback_preimageOpenDomain p (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  have hcomm : r₁ ≫ q = r₂ ≫ q := by
    apply (cancel_mono ιX).mp
    rw [Category.assoc, Category.assoc, hq.w, ← Category.assoc, ← Category.assoc,
      h₁.w, h₂, Category.assoc, Category.assoc, c.isPullback.w]
  have hrel : IsPullback r₁ r₂ q q := by
    have hfull : IsPullback r₁ (r₂ ≫ ιY) (q ≫ ιX) p := by
      rw [h₂, hq.w]
      exact h₁.paste_vert c.isPullback
    exact hfull.of_bot hcomm hq
  have hgraph (γ : Γ) :
      analyticDeckGraph hrel (c.restrictedDeck U γ) (c.restrictedDeck_over U γ) ≫ ιP =
        ιY ≫ c.graph γ := by
    apply c.isPullback.hom_ext
    · rw [Category.assoc, ← h₁.w, ← Category.assoc, analyticDeckGraph, hrel.lift_fst,
        Category.id_comp, Category.assoc, c.graph_fst, Category.comp_id]
    · rw [Category.assoc, ← h₂, ← Category.assoc, analyticDeckGraph, hrel.lift_snd,
        c.restrictedDeck_hom_comp, Category.assoc, c.graph_snd]
  have hgraphPoint (γ : Γ) (y : localizedSpaceFunctor.obj (domainObj Y D)) :
      (localizedSpaceFunctor.map (analyticDeckGraph hrel (c.restrictedDeck U γ)
        (c.restrictedDeck_over U γ)) y).val = localizedSpaceFunctor.map (c.graph γ) y.val := by
    have h := hgraph γ
    change _ ≫ domainι c.relation E = _ at h
    change @Eq (localizedSpaceFunctor.obj c.relation) _ _
    simpa only [Functor.map_comp, TopCat.comp_app, domainι_apply] using
      congrArg (fun f => localizedSpaceFunctor.map f y) h
  refine ⟨?_, ?_, c.restrictedDeck U, c.restrictedDeck_over U,
    domainObj c.relation E, r₁, r₂, hrel, ?_, ?_⟩
  · apply etale_of_comp_domainι _
    rw [hq.w]
    exact etale_comp (etaleOpenDomainStatement Y V hV) c.etale_map
  · intro x
    obtain ⟨y, hy⟩ := c.surjective x.val
    have hyU : localizedSpaceFunctor.map p y ∈ U := by rw [hy]; exact x.property
    let y' : localizedSpaceFunctor.obj (domainObj Y D) := ⟨y, hyU⟩
    have h := congrArg (fun f => localizedSpaceFunctor.map f y') hq.w
    simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h
    exact ⟨y', Subtype.ext (h.trans hy)⟩
  · intro t
    obtain ⟨γ, y, hy⟩ := c.covers t.val
    change localizedSpaceFunctor.map (c.graph γ) y = t.val at hy
    have hyt : localizedSpaceFunctor.map c.fst t.val = y := by
      rw [← hy, ← TopCat.comp_app, ← Functor.map_comp, c.graph_fst,
        localizedSpaceFunctor.map_id]
      rfl
    have hyV : y ∈ V := hyt ▸ (show localizedSpaceFunctor.map c.fst t.val ∈ V from t.property)
    let y' : localizedSpaceFunctor.obj (domainObj Y D) := ⟨y, hyV⟩
    exact ⟨γ, y', Subtype.ext ((hgraphPoint γ y').trans hy)⟩
  · intro γ δ hγδ
    apply Set.disjoint_left.mpr
    rintro t ⟨y, rfl⟩ ⟨z, hz⟩
    refine Set.disjoint_left.mp (c.disjoint_graphs hγδ) ⟨y.val, rfl⟩ ⟨z.val, ?_⟩
    exact ((hgraphPoint δ z).symm.trans (congrArg Subtype.val hz)).trans (hgraphPoint γ y)

/-- The open-restricted deck automorphisms commute with the inclusion into the
original source. -/
@[reassoc (attr := simp)]
theorem restrictOpen_deck_hom_comp (γ : Γ) :
    ((c.restrictOpen U).deck γ).asIso.hom ≫ ιY = ιY ≫ (c.deck γ).asIso.hom :=
  c.restrictedDeck_hom_comp U γ

end Langlands.Analytic.SaturatedAtlasPresentation.AnalyticGaloisCover
