import Langlands.GroupScheme.Reductive.AffinePinnedCentralizer
import Langlands.GroupScheme.AutomorphicAction.LocallyInnerTransport

/-! # Torus rigidity of locally inner comparisons preserving the cocharacter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A relative conjugator for an automorphism fixing the canonical
cocharacter is a point of the actual coordinate torus. -/
theorem existsUnique_torusConjugator
    {σ : M.groupOver f ≅ M.groupOver f}
    (hσ : M.cocharacterOver f ≫ σ.hom = M.cocharacterOver f)
    {V : Over T} (y : V ⟶ (M.groupOver f).X)
    (hy : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso σ y) :
    ∃! t : V ⟶ (splitTorus T M.coordinates).X,
      t ≫ (M.inclusionOver f).hom.hom = y := by
  have hcent : y ∈ (Dynamic.centralizer (M.cocharacterOver f)).carrier V := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    intro W a z
    have hc := hy a (z ≫ (M.cocharacterOver f).hom.hom)
    simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] at hc
    have hfix : (z ≫ (M.cocharacterOver f).hom.hom) ≫ σ.hom.hom.hom =
        z ≫ (M.cocharacterOver f).hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hσ]
    rw [hfix] at hc
    exact (mul_inv_eq_iff_eq_mul).mp hc
  rw [M.centralizer_cocharacterOver f, SubgroupFunctor.mem_range] at hcent
  obtain ⟨t, ht⟩ := hcent
  let : Mono (M.inclusionOver f).hom.hom := M.inclusionOver_mono f
  exact ⟨t, ht, fun s hs => (cancel_mono _).mp (hs.trans ht.symm)⟩

/-- The unique lift of a relative cocharacter-fixing conjugator to the actual
coordinate torus. No cover or rational lift is chosen here. -/
def torusConjugator
    {σ : M.groupOver f ≅ M.groupOver f}
    (hσ : M.cocharacterOver f ≫ σ.hom = M.cocharacterOver f)
    {V : Over T} (y : V ⟶ (M.groupOver f).X)
    (hy : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso σ y) :
    V ⟶ (splitTorus T M.coordinates).X :=
  (existsUnique_torusConjugator hσ y hy).choose

@[reassoc (attr := simp)]
theorem torusConjugator_comp
    {σ : M.groupOver f ≅ M.groupOver f}
    (hσ : M.cocharacterOver f ≫ σ.hom = M.cocharacterOver f)
    {V : Over T} (y : V ⟶ (M.groupOver f).X)
    (hy : (AutomorphicAction.conjugation (𝟙 (M.groupOver f))).RepresentsIso σ y) :
    torusConjugator hσ y hy ≫ (M.inclusionOver f).hom.hom = y :=
  (existsUnique_torusConjugator hσ y hy).choose_spec.1

/-- A locally inner automorphism fixing the canonical cocharacter fixes the
whole coordinate torus pointwise on every scheme test. -/
theorem inclusionOver_comp_eq_of_locallyInner
    {σ : M.groupOver f ≅ M.groupOver f}
    (hσ : M.cocharacterOver f ≫ σ.hom = M.cocharacterOver f)
    (hi : IsFppfLocallyInner σ) :
    M.inclusionOver f ≫ σ.hom = M.inclusionOver f := by
  obtain ⟨V, hf, hs, hl, y, hy⟩ := hi
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : LocallyOfFinitePresentation V.hom := hl
  let t := torusConjugator hσ y hy
  have ht : t ≫ (M.inclusionOver f).hom.hom = y := torusConjugator_comp hσ y hy
  apply hom_ext_points
  intro W z
  let Z : Over T := Over.mk (pullback.fst W.hom V.hom ≫ W.hom)
  let r : Z ⟶ W := Over.homMk (pullback.fst W.hom V.hom) rfl
  let a : Z ⟶ V := Over.homMk (pullback.snd W.hom V.hom) pullback.condition.symm
  have : Epi r.left := by
    change Epi (pullback.fst W.hom V.hom)
    infer_instance
  have : Epi r := Over.epi_of_epi_left r
  apply (cancel_epi r).mp
  have hc := hy a (r ≫ z ≫ (M.inclusionOver f).hom.hom)
  simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id] at hc
  rw [← ht, ← Category.assoc a t (M.inclusionOver f).hom.hom] at hc
  have hcomm : (a ≫ t ≫ (M.inclusionOver f).hom.hom) *
        (r ≫ z ≫ (M.inclusionOver f).hom.hom) =
      (r ≫ z ≫ (M.inclusionOver f).hom.hom) *
        (a ≫ t ≫ (M.inclusionOver f).hom.hom) := by
    simp only [← Category.assoc]
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  simp only [Category.assoc] at hc
  rw [hcomm, mul_inv_cancel_right] at hc
  simpa only [Grp.comp_hom_hom, Category.assoc] using hc.symm

/-- Inner-equivalent comparisons preserving the canonical cocharacters
induce exactly the same map on the entire coordinate torus. -/
theorem inclusionOver_comp_eq_of_innerEquivalent
    {e d : Comparison f g} (he : PreservesCocharacter e)
    (hd : PreservesCocharacter d) (hi : IsFppfInnerEquivalent e d) :
    M.inclusionOver f ≫ e.hom = M.inclusionOver f ≫ d.hom := by
  have hdinv : N.cocharacterOver g ≫ d.inv = M.cocharacterOver f := by
    rw [← hd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfix : M.cocharacterOver f ≫ (e ≪≫ d.symm).hom = M.cocharacterOver f := by
    change M.cocharacterOver f ≫ e.hom ≫ d.inv = M.cocharacterOver f
    rw [← Category.assoc, he, hdinv]
  have ht := inclusionOver_comp_eq_of_locallyInner hfix hi
  apply (cancel_mono d.inv).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using ht

end Langlands.GroupScheme.AffinePinnedModel
