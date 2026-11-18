import Langlands.GroupScheme.Descent.CechBaseChange
import Mathlib.CategoryTheory.HomCongr

/-! # Lifting Čech descent data from double and triple overlaps -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.CechBaseChange

variable {B S C V : Scheme.{u}} {p : S ⟶ B} {t : V ⟶ C} {q : V ⟶ S} {b : C ⟶ B}
variable {T T₀ W W₀ : Scheme.{u}} {G : GroupScheme S}

/-- Restrict a comparison of two pullbacks, changing the base of both endpoints. -/
def restrictHom (d : T₀ ⟶ T) {f g : T ⟶ S} {a c : T₀ ⟶ V}
    (hf : d ≫ f = a ≫ q) (hg : d ≫ g = c ≫ q)
    (e : (baseChange f).obj G ⟶ (baseChange g).obj G) :=
  reindexHom q a c (pullHom d hf hg e)

private theorem restrictHom_bijective (d : T₀ ⟶ T)
    {f g : T ⟶ S} {a c : T₀ ⟶ V} (hf : d ≫ f = a ≫ q) (hg : d ≫ g = c ≫ q)
    (h : Function.Bijective (fun e : (baseChange f).obj G ⟶ (baseChange g).obj G =>
      (baseChange d).map e)) :
    Function.Bijective (restrictHom d hf hg (G := G)) := by
  let e := ((pullbackComparison f d _ hf G) ≪≫ (pullbackComparison q a _ rfl G).symm).homCongr
    ((pullbackComparison g d _ hg G) ≪≫ (pullbackComparison q c _ rfl G).symm)
  have he : restrictHom d hf hg (G := G) =
      e ∘ fun z : (baseChange f).obj G ⟶ (baseChange g).obj G => (baseChange d).map z := by
    funext z
    simp only [Function.comp_apply, e, Iso.homCongr_apply, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, Iso.symm_hom, restrictHom, reindexHom, pullHom, Category.assoc]
  rw [he]
  exact e.bijective.comp h

private theorem restrictHom_comp (d : T₀ ⟶ T)
    {f g k : T ⟶ S} {a c j : T₀ ⟶ V}
    (hf : d ≫ f = a ≫ q) (hg : d ≫ g = c ≫ q) (hk : d ≫ k = j ≫ q)
    (e : (baseChange f).obj G ⟶ (baseChange g).obj G)
    (e' : (baseChange g).obj G ⟶ (baseChange k).obj G) :
    restrictHom d hf hk (e ≫ e') = restrictHom d hf hg e ≫ restrictHom d hg hk e' := by
  simp only [restrictHom, pullHom_comp d hf hg hk, reindexHom_comp]

private theorem pullHom_congr_map {d d' : T₀ ⟶ T} {f g : T ⟶ S} {a c : T₀ ⟶ S}
    (h : d = d') (hf : d ≫ f = a) (hg : d ≫ g = c)
    (hf' : d' ≫ f = a) (hg' : d' ≫ g = c)
    (e : (baseChange f).obj G ⟶ (baseChange g).obj G) :
    pullHom d hf hg e = pullHom d' hf' hg' e := by
  subst d'
  rfl

private theorem pullHom_restrictHom (d : T₀ ⟶ T) (r : W ⟶ T) (r₀ : W₀ ⟶ T₀)
    (d' : W₀ ⟶ W) (w : r₀ ≫ d = d' ≫ r)
    {f g : T ⟶ S} {a c : T₀ ⟶ V} (hf : d ≫ f = a ≫ q) (hg : d ≫ g = c ≫ q)
    {f' g' : W ⟶ S} {a' c' : W₀ ⟶ V}
    (hrf : r ≫ f = f') (hrg : r ≫ g = g') (hra : r₀ ≫ a = a') (hrc : r₀ ≫ c = c')
    (hdf : d' ≫ f' = a' ≫ q) (hdg : d' ≫ g' = c' ≫ q)
    (e : (baseChange f).obj G ⟶ (baseChange g).obj G) :
    pullHom r₀ hra hrc (restrictHom d hf hg e) =
      restrictHom d' hdf hdg (pullHom r hrf hrg e) := by
  simp only [restrictHom, pullHom_reindexHom, pullHom_pullHom]
  exact congrArg (reindexHom q a' c') (pullHom_congr_map w _ _ _ _ e)

private theorem cocycle_of_restricted_cocycle (w : q ≫ p = t ≫ b)
    (e : OverlapIso p G) (e₀ : OverlapIso t ((baseChange q).obj G))
    (he : restrictHom (overlapMap w) (overlapMap_fst w) (overlapMap_snd w) e.hom = e₀.hom)
    (hc : Cocycle e₀)
    (hi : Function.Injective (restrictHom (tripleMap w) (tripleMap_p1 w)
      (tripleMap_p3 w) (G := G))) : Cocycle e := by
  change pullHom (p12 p) rfl rfl e.hom ≫ pullHom (p23 p) (p23_fst p) rfl e.hom =
    pullHom (p13 p) (p13_fst p) (p13_snd p) e.hom
  apply hi
  rw [restrictHom_comp (tripleMap w) (tripleMap_p1 w) (tripleMap_p2 w) (tripleMap_p3 w)]
  have h12 := pullHom_restrictHom (overlapMap w) (p12 p) (p12 t) (tripleMap w)
    (tripleMap_p12 w).symm (overlapMap_fst w) (overlapMap_snd w)
    (rfl : p12 p ≫ fst p = p1 p) (rfl : p12 p ≫ snd p = p2 p)
    (rfl : p12 t ≫ fst t = p1 t) (rfl : p12 t ≫ snd t = p2 t)
    (tripleMap_p1 w) (tripleMap_p2 w) e.hom
  have h23 := pullHom_restrictHom (overlapMap w) (p23 p) (p23 t) (tripleMap w)
    (tripleMap_p23 w).symm (overlapMap_fst w) (overlapMap_snd w)
    (p23_fst p) (rfl : p23 p ≫ snd p = p3 p)
    (p23_fst t) (rfl : p23 t ≫ snd t = p3 t)
    (tripleMap_p2 w) (tripleMap_p3 w) e.hom
  have h13 := pullHom_restrictHom (overlapMap w) (p13 p) (p13 t) (tripleMap w)
    (tripleMap_p13 w).symm (overlapMap_fst w) (overlapMap_snd w)
    (p13_fst p) (p13_snd p) (p13_fst t) (p13_snd t)
    (tripleMap_p1 w) (tripleMap_p3 w) e.hom
  rw [he] at h12 h23 h13
  rw [← h12, ← h23, ← h13]
  exact hc

/-- A datum lifts along a square if reduction is bijective on the double-overlap
Hom sets and on the Hom set between the extreme coordinates of the triple overlap. -/
theorem exists_datum_reindex_eq (w : q ≫ p = t ≫ b)
    (D₀ : Datum t ((baseChange q).obj G))
    (h₂ : ∀ f g : Overlap p ⟶ S,
      Function.Bijective (fun e : (baseChange f).obj G ⟶ (baseChange g).obj G =>
        (baseChange (overlapMap w)).map e))
    (h₃ : Function.Bijective (fun e : (baseChange (p1 p)).obj G ⟶ (baseChange (p3 p)).obj G =>
      (baseChange (tripleMap w)).map e)) :
    ∃ D : Datum p G, D.reindex t q b w = D₀ := by
  have lift₁₂ := restrictHom_bijective (overlapMap w) (overlapMap_fst w) (overlapMap_snd w)
    (h₂ (fst p) (snd p))
  have lift₂₁ := restrictHom_bijective (overlapMap w) (overlapMap_snd w) (overlapMap_fst w)
    (h₂ (snd p) (fst p))
  obtain ⟨e, he⟩ := lift₁₂.surjective D₀.overlap.hom
  obtain ⟨e', he'⟩ := lift₂₁.surjective D₀.overlap.inv
  let E : OverlapIso p G :=
    { hom := e
      inv := e'
      hom_inv_id := by
        apply (restrictHom_bijective (overlapMap w) (overlapMap_fst w) (overlapMap_fst w)
          (h₂ (fst p) (fst p))).injective
        rw [restrictHom_comp (overlapMap w) (overlapMap_fst w) (overlapMap_snd w)
          (overlapMap_fst w), he, he']
        simp [restrictHom, reindexHom]
      inv_hom_id := by
        apply (restrictHom_bijective (overlapMap w) (overlapMap_snd w) (overlapMap_snd w)
          (h₂ (snd p) (snd p))).injective
        rw [restrictHom_comp (overlapMap w) (overlapMap_snd w) (overlapMap_fst w)
          (overlapMap_snd w), he', he]
        simp [restrictHom, reindexHom] }
  refine ⟨⟨E, cocycle_of_restricted_cocycle w E D₀.overlap he D₀.cocycle
    (restrictHom_bijective (tripleMap w) (tripleMap_p1 w) (tripleMap_p3 w) h₃).injective⟩, ?_⟩
  apply Datum.ext
  apply Iso.ext
  exact he

end Langlands.GroupScheme.Descent.CechBaseChange
