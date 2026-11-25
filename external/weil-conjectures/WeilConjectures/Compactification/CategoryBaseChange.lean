/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Cofiltered
public import WeilConjectures.Compactification.NagataCompactification

/-!

# Base change of the category of compactifications

Let `f : X ⟶ S` be a morphism of schemes and `t : T ⟶ S` a morphism of bases. Base change
along `t` sends a compactification `c` of `f` to the compactification `c.baseChange t` of
`f' = pullback.snd f t`, and a refinement `r : c ⟶ d` to its base change
`r.hom ×_S T : c.Z ×_S T ⟶ d.Z ×_S T`. This is a functor
`Compactification f ⥤ Compactification (pullback.snd f t)`; in particular it carries common
refinements to common refinements and equalizing refinements to equalizing refinements.

For the common refinement `inf c d` (the scheme-theoretic image of the graph of `X` in
`c.Z ×_S d.Z`), base change and the construction of `inf` commute up to a closed immersion:
the ambient scheme of `inf c' d'`, for `c' = c.baseChange t` and `d' = d.baseChange t`, is a
closed subscheme of that of `(inf c d).baseChange t`, and the inclusion is a refinement over
the two projections. If `t` is flat, the inclusion is an isomorphism.

Finally, over a field the category of compactifications of a separated morphism of
finite-type schemes is cofiltered.

## Main definitions

- `AlgebraicGeometry.Compactification.Refinement.baseChange`: the base change of a
  refinement;
- `AlgebraicGeometry.Compactification.baseChangeFunctor`: base change as a functor between
  categories of compactifications;
- `AlgebraicGeometry.Compactification.infBaseChange`: the refinement
  `inf c' d' ⟶ (inf c d).baseChange t` comparing the two ways of forming the common refinement
  after base change.

## Main results

- `AlgebraicGeometry.Compactification.isClosedImmersion_infBaseChange_hom`: the comparison is a
  closed immersion;
- `AlgebraicGeometry.Compactification.isIso_infBaseChange_hom`: along a flat base change it is
  an isomorphism, i.e. the common refinement commutes with flat base change;
- `AlgebraicGeometry.Compactification.isCofiltered_of_field`: over a field, the category of
  compactifications of a separated morphism of finite-type schemes is cofiltered.

## Blueprint

This file implements the base change part of
`proposition-dense-compactifications-form-cofiltered-category` and of
`remark-base-change-compactification--1`, and `prop-compactification-refinement`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}

namespace Refinement

variable {c d e : Compactification f}

/-- **Base change of a refinement** (blueprint
`proposition-dense-compactifications-form-cofiltered-category`,
`remark-base-change-compactification--1`): a refinement `r : c ⟶ d` of compactifications of `f` base
changes along `t : T ⟶ S` to the refinement `r.hom ×_S T` of `d.baseChange t` by
`c.baseChange t`. -/
@[simps]
noncomputable def baseChange (r : c.Refinement d) (t : T ⟶ S) :
    (c.baseChange t).Refinement (d.baseChange t) where
  hom := pullback.map c.g t d.g t r.hom (𝟙 T) (𝟙 S) (by rw [r.hom_g, Category.comp_id])
    (by simp)
  i_hom := by
    apply pullback.hom_ext
    · simp only [baseChange_Z, Category.assoc, limit.lift_π,
        PullbackCone.mk_π_app]
      rw [baseChange_i_fst_assoc, r.i_hom, baseChange_i_fst]
    · simp only [baseChange_Z, Category.assoc, limit.lift_π,
        PullbackCone.mk_π_app, Category.comp_id]
      rw [baseChange_i_snd, baseChange_i_snd]
  hom_g := by simp

@[simp]
lemma baseChange_id (c : Compactification f) (t : T ⟶ S) :
    (Refinement.id c).baseChange t = Refinement.id (c.baseChange t) := by
  ext1
  apply pullback.hom_ext <;> simp

lemma baseChange_comp (r : c.Refinement d) (s : d.Refinement e) (t : T ⟶ S) :
    (r.comp s).baseChange t = (r.baseChange t).comp (s.baseChange t) := by
  ext1
  apply pullback.hom_ext <;> simp

end Refinement

/-- **Base change of the category of compactifications** (blueprint
`proposition-dense-compactifications-form-cofiltered-category`,
`remark-base-change-compactification--1`): base change along `t : T ⟶ S` is a functor from
compactifications of `f` to compactifications of `f' = pullback.snd f t`. Being a functor, it
carries common refinements to common refinements and refinements equalizing two parallel refinements
to refinements equalizing their base changes. -/
@[simps]
noncomputable def baseChangeFunctor (t : T ⟶ S) :
    Compactification f ⥤ Compactification (pullback.snd f t) where
  obj c := c.baseChange t
  map r := Refinement.baseChange r t
  map_id c := Refinement.baseChange_id c t
  map_comp r s := Refinement.baseChange_comp r s t

/-! ### The common refinement and base change -/

section Inf

variable (c d : Compactification f) (t : T ⟶ S)

/-- The comparison morphism `c'.Z ×_T d'.Z ⟶ c.Z ×_S d.Z` between the ambient fibre products
of the common refinements, for `c' = c.baseChange t` and `d' = d.baseChange t`. -/
noncomputable def baseChangePullbackMap :
    pullback (c.baseChange t).g (d.baseChange t).g ⟶ pullback c.g d.g :=
  pullback.map _ _ _ _ (pullback.fst c.g t) (pullback.fst d.g t) t
    pullback.condition.symm pullback.condition.symm

@[reassoc (attr := simp)]
lemma baseChangePullbackMap_fst :
    baseChangePullbackMap c d t ≫ pullback.fst c.g d.g =
      pullback.fst (c.baseChange t).g (d.baseChange t).g ≫ pullback.fst c.g t :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangePullbackMap_snd :
    baseChangePullbackMap c d t ≫ pullback.snd c.g d.g =
      pullback.snd (c.baseChange t).g (d.baseChange t).g ≫ pullback.fst d.g t :=
  pullback.lift_snd _ _ _

/-- The graph of `X ×_S T` in `c'.Z ×_T d'.Z` lies over the graph of `X` in `c.Z ×_S d.Z`. -/
lemma graph_baseChange_baseChangePullbackMap :
    graph (c.baseChange t) (d.baseChange t) ≫ baseChangePullbackMap c d t =
      pullback.fst f t ≫ graph c d := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangePullbackMap_fst, graph_fst_assoc, baseChange_i_fst,
      Category.assoc, graph_fst]
  · rw [Category.assoc, baseChangePullbackMap_snd, graph_snd_assoc, baseChange_i_fst,
      Category.assoc, graph_snd]

variable [QuasiCompact f]

/-- The ambient morphism of `infBaseChange`. -/
noncomputable def infBaseChangeHom :
    (inf (c.baseChange t) (d.baseChange t)).Z ⟶ ((inf c d).baseChange t).Z :=
  pullback.lift
    (Scheme.Hom.imageMap _ _ (pullback.fst f t) (baseChangePullbackMap c d t)
      (graph_baseChange_baseChangePullbackMap c d t))
    ((graph (c.baseChange t) (d.baseChange t)).imageι ≫
      pullback.fst (c.baseChange t).g (d.baseChange t).g ≫ pullback.snd c.g t)
    (by
      change _ ≫ ((graph c d).imageι ≫ pullback.fst c.g d.g) ≫ c.g = _
      simp only [Category.assoc, Scheme.Hom.imageMap_imageι_assoc,
        baseChangePullbackMap_fst_assoc]
      rw [pullback.condition (f := c.g) (g := t)])

@[reassoc (attr := simp)]
lemma infBaseChangeHom_fst :
    infBaseChangeHom c d t ≫ pullback.fst (inf c d).g t =
      Scheme.Hom.imageMap _ _ (pullback.fst f t) (baseChangePullbackMap c d t)
        (graph_baseChange_baseChangePullbackMap c d t) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma infBaseChangeHom_snd :
    infBaseChangeHom c d t ≫ pullback.snd (inf c d).g t =
      (graph (c.baseChange t) (d.baseChange t)).imageι ≫
        pullback.fst (c.baseChange t).g (d.baseChange t).g ≫ pullback.snd c.g t :=
  pullback.lift_snd _ _ _

/-- **The common refinement commutes with base change up to a closed immersion** (blueprint
`remark-base-change-compactification--1`, base change, second part): for compactifications
`c`, `d` of a quasi-compact `f` and any `t : T ⟶ S`, the common refinement of the base changes
`c' = c.baseChange t` and `d' = d.baseChange t` refines the base change of the common
refinement of `c` and `d`. The ambient morphism is a closed immersion
(`isClosedImmersion_infBaseChange_hom`), an isomorphism if `t` is flat
(`isIso_infBaseChange_hom`), and the refinement lies over the two projections
(`infBaseChange_comp_infFst`, `infBaseChange_comp_infSnd`). -/
noncomputable def infBaseChange :
    (inf (c.baseChange t) (d.baseChange t)).Refinement ((inf c d).baseChange t) where
  hom := infBaseChangeHom c d t
  i_hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, infBaseChangeHom_fst, inf_i, Scheme.Hom.toImage_imageMap,
        baseChange_i_fst]
      rfl
    · rw [Category.assoc, infBaseChangeHom_snd, inf_i, Scheme.Hom.toImage_imageι_assoc,
        graph_fst_assoc, baseChange_i_snd, baseChange_i_snd]
  hom_g := by
    change _ ≫ pullback.snd (inf c d).g t = _
    rw [infBaseChangeHom_snd]
    rfl

lemma infBaseChange_hom : (infBaseChange c d t).hom = infBaseChangeHom c d t := rfl

/-- The comparison `infBaseChange` lies over the first projections. -/
theorem infBaseChange_comp_infFst :
    (infBaseChange c d t).comp ((infFst c d).baseChange t) =
      infFst (c.baseChange t) (d.baseChange t) := by
  ext1
  apply pullback.hom_ext
  · simp [infBaseChange_hom, infFst_hom]
  · simp only [Refinement.comp_hom, Refinement.baseChange_hom, infBaseChange_hom, infFst_hom,
      Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      Category.comp_id, infBaseChangeHom_snd]

/-- The comparison `infBaseChange` lies over the second projections. -/
theorem infBaseChange_comp_infSnd :
    (infBaseChange c d t).comp ((infSnd c d).baseChange t) =
      infSnd (c.baseChange t) (d.baseChange t) := by
  ext1
  apply pullback.hom_ext
  · simp [infBaseChange_hom, infSnd_hom]
  · simp only [Refinement.comp_hom, Refinement.baseChange_hom, infBaseChange_hom, infSnd_hom,
      Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      Category.comp_id, infBaseChangeHom_snd]
    change _ ≫ _ ≫ (c.baseChange t).g = _ ≫ _ ≫ (d.baseChange t).g
    rw [pullback.condition]

/-- The comparison `infBaseChange` is a closed immersion: the scheme-theoretic image computed
after base change is a closed subscheme of the base change of the scheme-theoretic image. -/
instance isClosedImmersion_infBaseChange_hom : IsClosedImmersion (infBaseChange c d t).hom := by
  let h : ((inf c d).baseChange t).Z ⟶ pullback (c.baseChange t).g (d.baseChange t).g :=
    pullback.lift ((infFst c d).baseChange t).hom ((infSnd c d).baseChange t).hom
      (by rw [((infFst c d).baseChange t).hom_g, ((infSnd c d).baseChange t).hom_g])
  have hh : (infBaseChange c d t).hom ≫ h =
      (graph (c.baseChange t) (d.baseChange t)).imageι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Refinement.comp_hom, infBaseChange_comp_infFst,
        infFst_hom]
    · rw [Category.assoc, pullback.lift_snd, ← Refinement.comp_hom, infBaseChange_comp_infSnd,
        infSnd_hom]
  have : IsSeparated (h ≫ pullback.fst _ _ ≫ (c.baseChange t).g) := by
    rw [pullback.lift_fst_assoc, ((infFst c d).baseChange t).hom_g]
    infer_instance
  have : IsSeparated h := .of_comp h (pullback.fst _ _ ≫ (c.baseChange t).g)
  have : IsClosedImmersion ((infBaseChange c d t).hom ≫ h) := by rw [hh]; infer_instance
  exact .of_comp _ h

/-- **The common refinement commutes with flat base change** (blueprint
`remark-base-change-compactification--1`): if `t` is flat, the comparison `infBaseChange` is an
isomorphism of ambient schemes. -/
instance isIso_infBaseChange_hom [Flat t] : IsIso (infBaseChange c d t).hom := by
  have : QuasiCompact (inf c d).i := (inf c d).quasiCompact_openImmersion inferInstance
  have : IsSchemeTheoreticallyDominant ((inf c d).baseChange t).i :=
    isSchemeTheoreticallyDominant_i_baseChange _ t (isSchemeTheoreticallyDominant_inf_i c d)
  refine IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (eq_bot_iff.mpr ?_)
  calc (infBaseChange c d t).hom.ker
      ≤ ((inf (c.baseChange t) (d.baseChange t)).i ≫ (infBaseChange c d t).hom).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = ((inf c d).baseChange t).i.ker := by rw [(infBaseChange c d t).i_hom]
    _ = ⊥ := ((inf c d).baseChange t).i.ker_eq_bot

end Inf

/-! ### Compactifications over a field -/

/-- **Compactifications over a field form a cofiltered category** (blueprint
`prop-compactification-refinement`): let `X` and `Y` be schemes of finite type over a field
`K` and `f : X ⟶ Y` a separated `K`-morphism (automatically of finite type). Then the
category of compactifications of `f` is nonempty, by Nagata's compactification theorem, and
cofiltered: any finite family of compactifications has a common refinement, and any two
parallel refinements become equal after a further refinement. -/
theorem isCofiltered_of_field {K : Type u} [Field K] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType pX] [QuasiCompact pX]
    [LocallyOfFiniteType pY] [QuasiCompact pY] (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [IsSeparated f] : IsCofiltered (Compactification f) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace pY
  have : QuasiSeparatedSpace Y := IsLocallyNoetherian.quasiSeparatedSpace
  have : LocallyOfFiniteType (f ≫ pY) := by rw [hf]; infer_instance
  have : QuasiCompact (f ≫ pY) := by rw [hf]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  have : QuasiCompact f := .of_comp f pY
  infer_instance

end AlgebraicGeometry.Compactification
