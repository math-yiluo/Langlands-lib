import Langlands.Geometry.Analytic.AnalyticGaloisCover
import Langlands.Geometry.Analytic.SchemeAnalytificationEtaleSite
import Langlands.Geometry.Analytic.SchemeAnalytificationPullbacks
import Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonProof

/-! # Analytification of algebraic étale Galois covers -/

noncomputable section

universe u z

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open SaturatedAtlasPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false
set_option autoImplicit false

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "S" => (separatedLocallyFiniteTypeOver K).FullSubcategory
local notation "F" => localizedAnalytification K
local notation "forgetScheme" => (separatedLocallyFiniteTypeOver K).ι ⋙ Over.forget _

private def analyticCenter (X : S) : localizedSpaceFunctor.obj ((F).obj X) → X.obj.left :=
  letI : LocallyOfFiniteType X.obj.hom := X.property.1
  center K X.obj.hom

private theorem range_map {Y X : S} (p : Y ⟶ X) :
    Set.range (localizedSpaceFunctor.map ((F).map p)) =
      analyticCenter K X ⁻¹' Set.range p.hom.left := by
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : IsSeparated Y.obj.hom := Y.property.2
  let : IsSeparated X.obj.hom := X.property.2
  change Set.range (localizedSpaceFunctor.map (Localized.map K Y.obj.hom X.obj.hom
    p.hom.left (Over.w p.hom))).hom = _
  rw [Localized.underlying_map]
  exact range_analytification K Y.obj.hom X.obj.hom p.hom.left (Over.w p.hom)

variable {Y X : (separatedLocallyFiniteTypeOver K).FullSubcategory}

private def selfPullback (p : Y ⟶ X) [Etale p.hom.left] : S := by
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : IsSeparated Y.obj.hom := Y.property.2
  let : IsSeparated p.hom.left := by
    have : IsSeparated (p.hom.left ≫ X.obj.hom) := Over.w p.hom ▸ Y.property.2
    exact IsSeparated.of_comp p.hom.left X.obj.hom
  let base := pullback.fst p.hom.left p.hom.left ≫ Y.obj.hom
  exact ⟨Over.mk base, inferInstanceAs (LocallyOfFiniteType base),
    inferInstanceAs (IsSeparated base)⟩

variable (p : Y ⟶ X) [Etale p.hom.left]

local notation "f" => p.hom.left
local notation "P" => pullback (C := Scheme) f f
local notation "pr₁" => pullback.fst f f
local notation "pr₂" => pullback.snd f f
local notation "R" => selfPullback K p

private def firstProjection : R ⟶ Y :=
  ObjectProperty.homMk (Over.homMk pr₁ rfl)

private def secondProjection : R ⟶ Y :=
  ObjectProperty.homMk (Over.homMk pr₂ (by
    change pr₂ ≫ Y.obj.hom = pr₁ ≫ Y.obj.hom
    rw [← Over.w p.hom, ← Category.assoc, ← Category.assoc, pullback.condition]))

variable {Γ : Type z} [Group Γ] (deck : Γ →* Aut Y)
  (hover : ∀ γ, (deck γ).asIso.hom ≫ p = p)

private abbrev schemeDeck (γ : Γ) : Aut Y.obj.left :=
  Functor.mapAut Y (forgetScheme) (deck γ)

local notation "d" => schemeDeck K deck

omit [IsUltrametricDist K] [CompleteSpace K] [Etale p.hom.left] in
include hover in
private theorem schemeDeck_over (γ : Γ) : (d γ).asIso.hom ≫ f = f :=
  (forgetScheme).congr_map (hover γ)

private def schemeGraph (γ : Γ) : Y.obj.left ⟶ P :=
  pullback.lift (𝟙 _) (d γ).asIso.hom ((Category.id_comp _).trans
    (schemeDeck_over K p deck hover γ).symm)

local notation "graph" => schemeGraph K p deck hover

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem graph_openImmersion (γ : Γ) : IsOpenImmersion (graph γ) := by
  let e := (d γ).asIso
  let t := pullback.map f f f f (𝟙 _) e.hom (𝟙 _) (by simp)
    ((Category.comp_id _).trans (schemeDeck_over K p deck hover γ).symm)
  have : IsIso e.hom := e.isIso_hom
  have : IsIso t := pullback.map_isIso _ _ _ _ _ _ _ _ _
  have hgraph : graph γ = pullback.diagonal f ≫ t := by
    apply pullback.hom_ext <;> simp [schemeGraph, t, e]
  rw [hgraph]
  infer_instance

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem mem_range_graph_iff (γ : Γ) (t : ↥(P)) :
    t ∈ Set.range (graph γ) ↔
      (P).fromSpecResidueField t ≫ pr₁ ≫ (d γ).asIso.hom =
        (P).fromSpecResidueField t ≫ pr₂ := by
  let point := (P).fromSpecResidueField t
  change t ∈ Set.range (graph γ) ↔ point ≫ pr₁ ≫ (d γ).asIso.hom = point ≫ pr₂
  constructor
  · intro ht
    have : IsOpenImmersion (graph γ) := graph_openImmersion K p deck hover γ
    have h : Set.range point ⊆ Set.range (graph γ) := by
      rw [Scheme.range_fromSpecResidueField]
      exact Set.singleton_subset_iff.mpr ht
    let a := IsOpenImmersion.lift (graph γ) point h
    have ha : a ≫ graph γ = point := IsOpenImmersion.lift_fac _ _ _
    rw [← ha]
    simp [schemeGraph]
  · intro h
    have ha : (point ≫ pr₁) ≫ graph γ = point := by
      apply pullback.hom_ext
      · simp [schemeGraph]
      · simpa only [Category.assoc, schemeGraph, pullback.lift_snd] using h
    have ht : t ∈ Set.range point := by
      rw [Scheme.range_fromSpecResidueField]
      rfl
    rw [← ha] at ht
    obtain ⟨x, hx⟩ := ht
    exact ⟨(point ≫ pr₁) x, hx⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem existsUnique_graph_point
    (transport : ∀ (L : Type u) [Field L] (a b : Spec (.of L) ⟶ Y.obj.left),
      a ≫ f = b ≫ f → ∃! γ : Γ, a ≫ (d γ).asIso.hom = b)
    (t : ↥(P)) : ∃! γ, t ∈ Set.range (graph γ) := by
  let a := (P).fromSpecResidueField t ≫ pr₁
  let b := (P).fromSpecResidueField t ≫ pr₂
  have hab : a ≫ f = b ≫ f := by simp only [a, b, Category.assoc, pullback.condition]
  obtain ⟨γ, hγ, huniq⟩ := transport ((P).residueField t) a b hab
  have hmem (δ : Γ) : t ∈ Set.range (graph δ) ↔ a ≫ (d δ).asIso.hom = b := by
    rw [mem_range_graph_iff, Category.assoc]
  exact ⟨γ, (hmem γ).mpr hγ, fun δ hδ => huniq δ ((hmem δ).mp hδ)⟩

include hover in
private def graphOver (γ : Γ) : Y ⟶ R :=
  ObjectProperty.homMk (Over.homMk (graph γ) (by
    change graph γ ≫ pr₁ ≫ Y.obj.hom = Y.obj.hom
    simp [schemeGraph]))

private theorem analyticPullback : IsPullback ((F).map (firstProjection K p))
    ((F).map (secondProjection K p)) ((F).map p) ((F).map p) :=
  localizedAnalytification_map_isPullback K (IsPullback.of_hasPullback f f)

local notation "analyticDeck" => Functor.mapAut Y (F)

omit [Etale p.hom.left] in
include hover in
private theorem analyticDeck_over (γ : Γ) :
    (analyticDeck (deck γ)).asIso.hom ≫ (F).map p = (F).map p := by
  change (F).map (deck γ).asIso.hom ≫ (F).map p = (F).map p
  rw [← Functor.map_comp, hover γ]

private theorem map_graphOver (γ : Γ) : (F).map (graphOver K p deck hover γ) =
    analyticDeckGraph (analyticPullback K p) (analyticDeck (deck γ))
      (analyticDeck_over K p deck hover γ) := by
  apply (analyticPullback K p).hom_ext
  · rw [analyticDeckGraph, IsPullback.lift_fst, ← Functor.map_comp, ← (F).map_id Y]
    congr 1
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    simp [graphOver, firstProjection, schemeGraph]
  · rw [analyticDeckGraph, IsPullback.lift_snd, ← Functor.map_comp]
    change (F).map (graphOver K p deck hover γ ≫ secondProjection K p) =
      (F).map (deck γ).asIso.hom
    congr 1
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change graph γ ≫ pr₂ = (d γ).asIso.hom
    exact pullback.lift_snd _ _ _

/-- The analytification of a surjective algebraic étale map with a simply transitive
 deck action on field-valued fibres is an analytic Galois cover. -/
def analytificationGaloisCover (surjective : Function.Surjective f)
    (transport : ∀ (L : Type u) [Field L] (a b : Spec (.of L) ⟶ Y.obj.left),
      a ≫ f = b ≫ f → ∃! γ : Γ, a ≫ (d γ).asIso.hom = b) :
    AnalyticGaloisCover Γ ((F).map p) where
  etale_map := by
    let : LocallyOfFiniteType Y.obj.hom := Y.property.1
    let : LocallyOfFiniteType X.obj.hom := X.property.1
    let : IsSeparated Y.obj.hom := Y.property.2
    let : IsSeparated X.obj.hom := X.property.2
    exact Localized.etale_map K Y.obj.hom X.obj.hom strongEtaleSmallIndexComparison f (Over.w p.hom)
  surjective := Set.range_eq_univ.mp (by rw [range_map, surjective.range_eq, Set.preimage_univ])
  deck := (analyticDeck).comp deck
  deck_over := analyticDeck_over K p deck hover
  relation := (F).obj R
  fst := (F).map (firstProjection K p)
  snd := (F).map (secondProjection K p)
  isPullback := analyticPullback K p
  covers := by
    intro t
    obtain ⟨γ, hγ, -⟩ := existsUnique_graph_point K p deck hover transport (analyticCenter K R t)
    have ht : t ∈ Set.range (localizedSpaceFunctor.map ((F).map (graphOver K p deck hover γ))) := by
      rwa [range_map]
    rw [map_graphOver K p deck hover γ] at ht
    obtain ⟨y, hy⟩ := ht
    exact ⟨γ, y, hy⟩
  disjoint_graphs := by
    intro γ δ hne
    apply Set.disjoint_left.mpr
    intro t hγ hδ
    change t ∈ Set.range (localizedSpaceFunctor.map (analyticDeckGraph (analyticPullback K p)
      (analyticDeck (deck γ)) (analyticDeck_over K p deck hover γ))) at hγ
    change t ∈ Set.range (localizedSpaceFunctor.map (analyticDeckGraph (analyticPullback K p)
      (analyticDeck (deck δ)) (analyticDeck_over K p deck hover δ))) at hδ
    rw [← map_graphOver K p deck hover γ, range_map K] at hγ
    rw [← map_graphOver K p deck hover δ, range_map K] at hδ
    obtain ⟨σ, -, huniq⟩ := existsUnique_graph_point K p deck hover transport (analyticCenter K R t)
    exact hne ((huniq γ hγ).trans (huniq δ hδ).symm)

end Langlands.Analytic.SchemeAnalytification
