import Langlands.GroupScheme.FppfSubgroupComparison
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.FppfHomLocality

/-! # Torus and cocharacter laws for actual pinned-model comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N K : AffinePinnedModel.{u}} {T W : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base} {h : T ⟶ K.base}

/-- The actual torus-square clause for a comparison. -/
def PreservesTorus (e : Comparison f g) : Prop :=
  ∃ τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates,
    M.inclusionOver f ≫ e.hom = τ.hom ≫ N.inclusionOver g

/-- The actual positive-coroot cocharacter clause for a comparison. -/
def PreservesCocharacter (e : Comparison f g) : Prop :=
  M.cocharacterOver f ≫ e.hom = N.cocharacterOver g

/-- Closedness of the original torus inclusion gives monicity after pullback. -/
theorem inclusionOver_mono (M : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) : Mono (M.inclusionOver f).hom.hom := by
  let : IsClosedImmersion M.inclusion.hom.hom.left := M.closed
  let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Mono ((baseChange f).map M.inclusion).hom.hom := by
    change Mono ((Over.pullback f).map M.inclusion.hom.hom)
    infer_instance
  change Mono ((splitTorus.baseChangeIso f M.coordinates).inv.hom.hom ≫
    ((baseChange f).map M.inclusion).hom.hom)
  infer_instance

/-- Direct and iterated normalized torus inclusions agree. -/
theorem inclusionOver_pull (M : AffinePinnedModel.{u}) {T W : Scheme.{u}}
    (f : T ⟶ M.base) (q : W ⟶ T) :
    BasedBorelTransport.baseChangeInclusion q (M.inclusionOver f) ≫
        (baseChangeCompIso f q M.group).inv = M.inclusionOver (q ≫ f) := by
  have ht := splitTorus.baseChangeTorusHom_comp f q M.coordinates M.group M.inclusion
  simpa only [BasedBorelTransport.baseChangeInclusion, inclusionOver,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun k => k ≫ (baseChangeCompIso f q M.group).inv) ht

/-- The model cocharacter is the normalized pullback of the original one. -/
theorem cocharacterOver_eq_baseChange (M : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) :
    M.cocharacterOver f = Dynamic.baseChangeCocharacter f
      (BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis) :=
  (BasedBorelTransport.cocharacter_baseChange f M.inclusion M.rootDatum M.basis).symm

/-- Direct and iterated normalized model cocharacters agree. -/
theorem cocharacterOver_pull (M : AffinePinnedModel.{u}) {T W : Scheme.{u}}
    (f : T ⟶ M.base) (q : W ⟶ T) :
    Dynamic.baseChangeCocharacter q (M.cocharacterOver f) ≫
        (baseChangeCompIso f q M.group).inv = M.cocharacterOver (q ≫ f) := by
  simpa only [cocharacterOver_eq_baseChange, Descent.pullbackComparison,
    eqToIso_refl, Iso.trans_refl, Iso.symm_hom] using
    Dynamic.baseChangeCocharacter_tower f q (q ≫ f) rfl
      (BasedBorelTransport.cocharacter M.inclusion M.rootDatum M.basis)

@[simp] theorem preservesTorus_refl (M : AffinePinnedModel.{u})
    (f : T ⟶ M.base) : PreservesTorus (Iso.refl (M.groupOver f)) := by
  exact ⟨Iso.refl _, by simp⟩

@[simp] theorem preservesCocharacter_refl (M : AffinePinnedModel.{u})
    (f : T ⟶ M.base) : PreservesCocharacter (Iso.refl (M.groupOver f)) := by
  simp [PreservesCocharacter]

/-- Torus squares compose through actual torus isomorphisms. -/
theorem PreservesTorus.trans {e : Comparison f g} {d : Comparison g h}
    (he : PreservesTorus e) (hd : PreservesTorus d) : PreservesTorus (e ≪≫ d) := by
  obtain ⟨τ, hτ⟩ := he
  obtain ⟨σ, hσ⟩ := hd
  refine ⟨τ ≪≫ σ, ?_⟩
  simp only [Iso.trans_hom]
  rw [← Category.assoc, hτ, Category.assoc, hσ, ← Category.assoc]

/-- Cocharacter transport composes. -/
theorem PreservesCocharacter.trans {e : Comparison f g} {d : Comparison g h}
    (he : PreservesCocharacter e) (hd : PreservesCocharacter d) :
    PreservesCocharacter (e ≪≫ d) := by
  change M.cocharacterOver f ≫ e.hom ≫ d.hom = K.cocharacterOver h
  rw [← Category.assoc, he]
  exact hd

/-- Torus preservation is stable under arbitrary actual pullback. -/
theorem PreservesTorus.pull {e : Comparison f g} (he : PreservesTorus e)
    (q : W ⟶ T) : PreservesTorus (pullComparison e q) := by
  obtain ⟨τ, hτ⟩ := he
  refine ⟨(splitTorus.baseChangeIso q M.coordinates).symm ≪≫
    (baseChange q).mapIso τ ≪≫ splitTorus.baseChangeIso q N.coordinates, ?_⟩
  rw [← inclusionOver_pull M f q, ← inclusionOver_pull N g q]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    BasedBorelTransport.baseChangeInclusion, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, hτ, Functor.map_comp]
  simp only [Category.assoc]

/-- Cocharacter preservation is stable under arbitrary actual pullback. -/
theorem PreservesCocharacter.pull {e : Comparison f g}
    (he : PreservesCocharacter e) (q : W ⟶ T) :
    PreservesCocharacter (pullComparison e q) := by
  change M.cocharacterOver (q ≫ f) ≫ (pullComparison e q).hom =
    N.cocharacterOver (q ≫ g)
  rw [← cocharacterOver_pull M f q, ← cocharacterOver_pull N g q]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Dynamic.baseChangeCocharacter_comp_hom, he]

/-- One arbitrary fppf cover detects the cocharacter clause. -/
theorem PreservesCocharacter.of_pull {e : Comparison f g} (q : W ⟶ T)
    [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (he : PreservesCocharacter (pullComparison e q)) : PreservesCocharacter e := by
  apply hom_ext_of_pointwise_fppf_baseChange
  intro s
  refine ⟨W, q, inferInstance, inferInstance, q.surjective s, ?_⟩
  apply (cancel_epi (Gm.baseChangeIso q).inv).mp
  change Dynamic.baseChangeCocharacter q (M.cocharacterOver f ≫ e.hom) =
    Dynamic.baseChangeCocharacter q (N.cocharacterOver g)
  apply (cancel_mono (baseChangeCompIso g q N.group).inv).mp
  change M.cocharacterOver (q ≫ f) ≫ (pullComparison e q).hom =
    N.cocharacterOver (q ≫ g) at he
  rw [← cocharacterOver_pull M f q, ← cocharacterOver_pull N g q] at he
  simpa only [Dynamic.baseChangeCocharacter_comp_hom, pullComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc] using he

/-- One arbitrary fppf cover detects the actual torus-square clause. -/
theorem PreservesTorus.of_pull {e : Comparison f g} (q : W ⟶ T)
    [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (he : PreservesTorus (pullComparison e q)) : PreservesTorus e := by
  obtain ⟨τ, hτ⟩ := he
  let σ := splitTorus.baseChangeIso q M.coordinates ≪≫ τ ≪≫
    (splitTorus.baseChangeIso q N.coordinates).symm
  have hσ : (baseChange q).map (M.inclusionOver f) ≫ (baseChange q).map e.hom =
      σ.hom ≫ (baseChange q).map (N.inclusionOver g) := by
    apply (cancel_epi (splitTorus.baseChangeIso q M.coordinates).inv).mp
    apply (cancel_mono (baseChangeCompIso g q N.group).inv).mp
    rw [← inclusionOver_pull M f q, ← inclusionOver_pull N g q] at hτ
    simpa only [σ, pullComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, BasedBorelTransport.baseChangeInclusion,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using hτ
  let : Mono (N.inclusionOver g).hom.hom := N.inclusionOver_mono g
  let : Flat (Over.mk q).hom := inferInstanceAs (Flat q)
  let : Surjective (Over.mk q).hom := inferInstanceAs (Surjective q)
  let : LocallyOfFinitePresentation (Over.mk q).hom :=
    inferInstanceAs (LocallyOfFinitePresentation q)
  obtain ⟨ρ, hρ, _⟩ := LocalGroupIso.existsUnique_iso_of_baseChange_square
    (U := Over.mk q) (M.inclusionOver f) (N.inclusionOver g) e σ hσ
  exact ⟨ρ, hρ⟩

end Langlands.GroupScheme.AffinePinnedModel
