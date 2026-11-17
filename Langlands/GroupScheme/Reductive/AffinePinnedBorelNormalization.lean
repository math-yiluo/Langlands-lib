import Langlands.GroupScheme.Reductive.AffinePinnedBorel
import Langlands.GroupScheme.RelativeLevi.BorelConjugacyProof
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Inner Borel alignment of actual pinned models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N K : AffinePinnedModel.{u}} {T W : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base} {h : T ⟶ K.base}

/-- The actual square between the canonical Borel inclusions. -/
def PreservesBorel (e : Comparison f g) : Prop :=
  ∃ β : M.borelOver f ≅ N.borelOver g,
    M.borelInclusionOver f ≫ e.hom = β.hom ≫ N.borelInclusionOver g

@[simp] theorem preservesBorel_refl (M : AffinePinnedModel.{u})
    (f : T ⟶ M.base) : PreservesBorel (Iso.refl (M.groupOver f)) := by
  exact ⟨Iso.refl _, by simp⟩

/-- Squares for the actual canonical Borels compose. -/
theorem PreservesBorel.trans {e : Comparison f g} {d : Comparison g h}
    (he : PreservesBorel e) (hd : PreservesBorel d) : PreservesBorel (e ≪≫ d) := by
  obtain ⟨β, hβ⟩ := he
  obtain ⟨σ, hσ⟩ := hd
  refine ⟨β ≪≫ σ, ?_⟩
  simp only [Iso.trans_hom]
  rw [← Category.assoc, hβ, Category.assoc, hσ, ← Category.assoc]

/-- The canonical-Borel square persists under arbitrary actual pullback. -/
theorem PreservesBorel.pull {e : Comparison f g} (he : PreservesBorel e)
    (q : W ⟶ T) : PreservesBorel (pullComparison e q) := by
  obtain ⟨β, hβ⟩ := he
  refine ⟨baseChangeCompIso f q M.borel ≪≫
    (baseChange q).mapIso β ≪≫ (baseChangeCompIso g q N.borel).symm, ?_⟩
  rw [← borelInclusionOver_pull M f q, ← borelInclusionOver_pull N g q]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, hβ, Functor.map_comp]
  simp only [Category.assoc]

/-- Conjugation by a point of the actual Borel preserves it. -/
theorem preservesBorel_inner (N : AffinePinnedModel.{u}) (g : T ⟶ N.base)
    (c : Over.mk (𝟙 T) ⟶ (N.borelOver g).X) :
    PreservesBorel ((N.groupOver g).innerIso (c ≫ (N.borelInclusionOver g).hom.hom)) := by
  exact ⟨(N.borelOver g).innerIso c,
    (innerIso_hom_comp (N.borelInclusionOver g) c).symm⟩

/-- A target inner conjugation aligns the canonical Borels on an etale cover. -/
def HasEtaleBorelNormalization (e : Comparison f g) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T,
    ∀ j, ∃ c : Over.mk (𝟙 (𝒰.X j)) ⟶ (N.groupOver (𝒰.f j ≫ g)).X,
      PreservesBorel
        (pullComparison e (𝒰.f j) ≪≫ (N.groupOver (𝒰.f j ≫ g)).innerIso c)

/-- Apply arbitrary-base relative Borel conjugacy and keep the actual
isomorphism of the Borel sources after normalized pullback. -/
theorem hasEtaleBorelNormalization (e : Comparison f g) :
    HasEtaleBorelNormalization e := by
  obtain ⟨𝒰, h𝒰⟩ := relativeBorelEtaleLocalConjugacyStatement T
    (N.groupOver g) (M.borelOver f) (N.borelOver g)
    (M.borelInclusionOver f ≫ e.hom) (N.borelInclusionOver g)
    (N.reductive.baseChange g)
    ((M.isRelativeBorel_borelInclusionOver f).comp_iso e)
    (N.isRelativeBorel_borelInclusionOver g)
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨c, hc⟩ := h𝒰 j
  let q := 𝒰.f j
  let k := (baseChange q).map (M.borelInclusionOver f ≫ e.hom) ≫
    (((baseChange q).obj (N.groupOver g)).innerIso c).hom
  let l := (baseChange q).map (N.borelInclusionOver g)
  have hk : IsRelativeBorelSubgroup k :=
    ((((M.isRelativeBorel_borelInclusionOver f).comp_iso e).baseChange
      (N.reductive.baseChange g) q).comp_iso _)
  have hl : IsRelativeBorelSubgroup l :=
    (N.isRelativeBorel_borelInclusionOver g).baseChange (N.reductive.baseChange g) q
  have hr : (SubgroupFunctor.range l).IsRepresentedBy k :=
    ⟨hk.isRelativeParabolicSubgroup.mono, hc⟩
  have hlr : (SubgroupFunctor.range l).IsRepresentedBy l :=
    ⟨hl.isRelativeParabolicSubgroup.mono, rfl⟩
  let β := hr.isoOfIsRepresentedBy hlr
  have hβ : k = β.hom ≫ l := (hr.isoOfIsRepresentedBy_hom_comp hlr).symm
  dsimp only [k, l] at hβ
  let cD := c ≫ (baseChangeCompIso g q N.group).inv.hom.hom
  refine ⟨cD, baseChangeCompIso f q M.borel ≪≫ β ≪≫
    (baseChangeCompIso g q N.borel).symm, ?_⟩
  change M.borelInclusionOver (q ≫ f) ≫
    ((pullComparison e q).hom ≫ ((N.groupOver (q ≫ g)).innerIso cD).hom) = _
  rw [← borelInclusionOver_pull M f q, ← borelInclusionOver_pull N g q]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← innerIso_hom_comp, ← Functor.map_comp_assoc,
    ← Category.assoc _ _ (baseChangeCompIso g q N.group).inv, hβ]
  simp only [Category.assoc]

end Langlands.GroupScheme.AffinePinnedModel
