import Langlands.Geometry.Analytic.AnalyticOpenImmersionBaseChange
import Langlands.Geometry.Analytic.EtaleSectionsOpen
import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints

/-! # Analytic étale Galois coverings given by deck graphs -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {Y X P : LocalizedCategory.{u, v, v} (K := K)}
  {p : Y ⟶ X} {fst snd : P ⟶ Y}

/-- The graph of a deck automorphism in the analytic self-pullback of the cover. -/
def analyticDeckGraph (h : IsPullback fst snd p p) (e : Aut Y)
    (he : e.asIso.hom ≫ p = p) : Y ⟶ P :=
  h.lift (𝟙 Y) e.asIso.hom ((Category.id_comp _).trans he.symm)

/-- A surjective étale map with deck automorphisms whose graphs partition the
underlying space of its analytic self-pullback. -/
structure AnalyticGaloisCover (Γ : Type z) [Group Γ] (p : Y ⟶ X) where
  etale_map : etale p
  surjective : Function.Surjective (localizedSpaceFunctor.map p)
  deck : Γ →* Aut Y
  deck_over : ∀ γ, (deck γ).asIso.hom ≫ p = p
  relation : LocalizedCategory.{u, v, v} (K := K)
  fst : relation ⟶ Y
  snd : relation ⟶ Y
  isPullback : IsPullback fst snd p p
  covers : ∀ t : localizedSpaceFunctor.obj relation, ∃ (γ : Γ) (y : localizedSpaceFunctor.obj Y),
    localizedSpaceFunctor.map (analyticDeckGraph isPullback (deck γ) (deck_over γ)) y = t
  disjoint_graphs : Pairwise fun γ δ : Γ =>
    Disjoint (range (localizedSpaceFunctor.map (analyticDeckGraph isPullback (deck γ) (deck_over γ))))
      (range (localizedSpaceFunctor.map (analyticDeckGraph isPullback (deck δ) (deck_over δ))))

namespace AnalyticGaloisCover

variable {Γ : Type z} [Group Γ] (c : AnalyticGaloisCover Γ p)

/-- The graph of a particular deck element. -/
def graph (γ : Γ) : Y ⟶ c.relation :=
  analyticDeckGraph c.isPullback (c.deck γ) (c.deck_over γ)

@[reassoc (attr := simp)]
theorem graph_fst (γ : Γ) : c.graph γ ≫ c.fst = 𝟙 Y :=
  c.isPullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd (γ : Γ) : c.graph γ ≫ c.snd = (c.deck γ).asIso.hom :=
  c.isPullback.lift_snd _ _ _

/-- Each deck graph identifies its source with an open analytic domain. -/
theorem openImmersion_graph (γ : Γ) : openImmersion (c.graph γ) := by
  let e := (c.deck γ).asIso
  have he : e.inv ≫ p = p := by
    calc
      _ = e.inv ≫ e.hom ≫ p := congrArg (e.inv ≫ ·) (c.deck_over γ).symm
      _ = _ := e.inv_hom_id_assoc p
  have h : IsPullback c.fst (c.snd ≫ e.inv) p p :=
    c.isPullback.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
      (by simp) (Category.id_comp _).symm (by simp) ((Category.comp_id _).trans he.symm)
  let d := h.lift (𝟙 Y) (𝟙 Y) rfl
  have hd : d = c.graph γ := by
    apply c.isPullback.hom_ext
    · exact (h.lift_fst _ _ _).trans (c.graph_fst γ).symm
    · have : IsIso e.inv := e.isIso_inv
      apply (cancel_mono e.inv).mp
      calc
        (d ≫ c.snd) ≫ e.inv = 𝟙 Y := (Category.assoc _ _ _).trans (h.lift_snd _ _ _)
        _ = (c.graph γ ≫ c.snd) ≫ e.inv := by rw [c.graph_snd, e.hom_inv_id]
  exact hd ▸ openImmersion_etale_diagonal h c.etale_map

/-- Any two ordinary points in the same fibre differ by a deck element. -/
theorem fibre_transitive (x y : localizedSpaceFunctor.obj Y)
    (hxy : localizedSpaceFunctor.map p x = localizedSpaceFunctor.map p y) :
    ∃ γ : Γ, localizedSpaceFunctor.map (c.deck γ).asIso.hom x = y := by
  obtain ⟨t, ht₁, ht₂⟩ := exists_point_of_isPullback_of_etale c.isPullback c.etale_map x y hxy
  obtain ⟨γ, s, hs⟩ := c.covers t
  change localizedSpaceFunctor.map (c.graph γ) s = t at hs
  have h₁ := congrArg (fun k : Y ⟶ Y => localizedSpaceFunctor.map k s) (c.graph_fst γ)
  have h₂ := congrArg (fun k : Y ⟶ Y => localizedSpaceFunctor.map k s) (c.graph_snd γ)
  simp only [Functor.map_comp, TopCat.comp_app, hs] at h₁ h₂
  have hsx : s = x := h₁.symm.trans ht₁
  exact ⟨γ, hsx ▸ h₂.symm.trans ht₂⟩

/-- Parallel arrows over the base agree up to a deck transformation on an
open neighborhood of each source point. -/
theorem exists_open_deck_eq {T : LocalizedCategory.{u, v, v} (K := K)}
    (a b : T ⟶ Y) (hab : a ≫ p = b ≫ p) (x : localizedSpaceFunctor.obj T) :
    ∃ (U : Set (localizedSpaceFunctor.obj T)) (hU : IsOpen U), x ∈ U ∧
      ∃ γ : Γ, domainι T ((presentationOf T).openDomain U hU) ≫ b =
        domainι T ((presentationOf T).openDomain U hU) ≫ a ≫ (c.deck γ).asIso.hom := by
  let m := c.isPullback.lift a b hab
  obtain ⟨γ, y, hy⟩ := c.covers (localizedSpaceFunctor.map m x)
  change localizedSpaceFunctor.map (c.graph γ) y = localizedSpaceFunctor.map m x at hy
  obtain ⟨O, hO, e, he⟩ := c.openImmersion_graph γ
  let U : Set (localizedSpaceFunctor.obj T) := localizedSpaceFunctor.map m ⁻¹' O
  have hU : IsOpen U := hO.preimage (localizedSpaceFunctor.map m).hom.continuous
  have hx : x ∈ U := by
    change localizedSpaceFunctor.map m x ∈ O
    rw [← hy, ← he, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact (localizedSpaceFunctor.map e.hom y).property
  let D := preimageOpenDomain m O hO
  let j := domainι T D
  let n := preimageOpenDomainMap m O hO ≫ e.inv
  have hm : n ≫ c.graph γ = j ≫ m := by
    change (preimageOpenDomainMap m O hO ≫ e.inv) ≫ c.graph γ = _
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]
    exact preimageOpenDomainMap_comp m O hO
  have ha : j ≫ a = n := by
    rw [← c.isPullback.lift_fst a b hab, ← Category.assoc, ← hm, Category.assoc,
      c.graph_fst, Category.comp_id]
  have hb : j ≫ b = n ≫ (c.deck γ).asIso.hom := by
    rw [← c.isPullback.lift_snd a b hab, ← Category.assoc, ← hm, Category.assoc, c.graph_snd]
  exact ⟨U, hU, hx, γ, hb.trans ((congrArg (· ≫ (c.deck γ).asIso.hom) ha).symm.trans
    (Category.assoc _ _ _))⟩

end AnalyticGaloisCover
end Langlands.Analytic.SaturatedAtlasPresentation
