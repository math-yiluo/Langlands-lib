/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant

/-!
# Effectivity of descent data is local

Let `p : X ⟶ Y` be faithfully flat and quasi-compact and let `D` be a descent datum on a scheme
`V` over `X` relative to `p`. If every point of `V` has an invariant open neighbourhood on which
`D` is effective, then `D` is effective
(`CategoryTheory.Over.DescentDatum.isEffective_of_forall_exists_mem`).

## Proof sketch

Let `J` be the set of invariant open subschemes `W ⊆ V` on which `D` is effective, ordered by
inclusion; it is a lower set among invariant opens, in particular closed under intersections.
For every `W : J` we choose a descended scheme `V W` over `Y`. Full faithfulness of base change
on descent data upgrades the inclusions `W ⊆ W'` to open immersions `V W ⟶ V W'`, and the
points of `V W` are the orbits of the points of `W`; this identifies the diagram of the `V W`
as a locally directed diagram of open immersions, so its colimit `V₀` exists. The maps
`W ⟶ V W ×_Y X ⟶ V₀ ×_Y X` glue to a map `V ⟶ V₀ ×_Y X`, which is a local isomorphism, injective
and surjective, hence an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {D : DescentDatum p V}

section Saturation

variable {U : V.left.Opens} {hU : D.IsInvariant U} {V₀ : Over Y} {q : U.toScheme ⟶ V₀.left}
  (hq : IsPullback q (U.ι ≫ V.hom) V₀.hom p)
  (hinv : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)),
    ((D.restrict U hU).transport f₁ f₂ h a).left ≫ q = a.left ≫ q)

include hq hinv in
/-- **Invariant opens are saturated.** If `D` is effective on the invariant open `U`, with
projection `q`, two points of `U` with the same image under `q` lie in the same invariant open
subschemes of `V`. -/
lemma mem_of_apply_eq_apply {O : V.left.Opens} (hO : D.IsInvariant O) {w w' : U}
    (hww' : q w = q w') (hw' : (w' : V.left) ∈ O) : (w : V.left) ∈ O := by
  obtain ⟨t, ht₁, ht₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := q) (g := q) w' w hww'.symm
  let T := (pullback.fst q q ≫ U.ι) ⁻¹ᵁ O
  have ht : t ∈ T := by
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, ht₁]
    exact hw'
  have hp : (T.ι ≫ pullback.fst q q ≫ U.ι ≫ V.hom) ≫ p =
      (T.ι ≫ pullback.snd q q ≫ U.ι ≫ V.hom) ≫ p := by
    simp only [Category.assoc, ← hq.w, pullback.condition_assoc]
  have he := (D.restrict U hU).transport_eq_of_isPullback hq hinv _ _ hp
    (Over.homMk (T.ι ≫ pullback.fst q q) (by simp))
    (Over.homMk (T.ι ≫ pullback.snd q q) (by simp)) (by simp [pullback.condition])
  have hl := restrict_transport_left_ι U hU _ _ hp (Over.homMk (T.ι ≫ pullback.fst q q) (by simp))
  rw [he] at hl
  have hr := hO _ _ hp (Over.homMk ((Over.homMk (T.ι ≫ pullback.fst q q) (by simp) :
      Over.mk (T.ι ≫ pullback.fst q q ≫ U.ι ≫ V.hom) ⟶ Over.mk (U.ι ≫ V.hom)).left ≫ U.ι)
      (by simp)) (by
    rintro _ ⟨s, rfl⟩
    exact s.2)
  rw [← hl] at hr
  refine hr ⟨⟨t, ht⟩, ?_⟩
  simp [ht₂]

end Saturation

/-- The restriction of `D` to `U'` is the restriction of the restriction of `D` to `U ⊇ U'`. -/
@[reassoc]
lemma restrict_transport_left_homOfLE {U U' : V.left.Opens} (hU : D.IsInvariant U)
    (hU' : D.IsInvariant U') (hle : U' ≤ U) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
    (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk (U'.ι ≫ V.hom)) :
    ((D.restrict U' hU').transport f₁ f₂ h a).left ≫ V.left.homOfLE hle =
      ((D.restrict U hU).transport f₁ f₂ h
        (Over.homMk (a.left ≫ V.left.homOfLE hle) (by simpa using Over.w a))).left := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, restrict_transport_left_ι,
    restrict_transport_left_ι]
  exact D.transport_left_congr' _ _ rfl rfl _ _ (by simp)

/-- **Effectivity passes to smaller invariant opens.** -/
lemma isEffective_restrict_of_le [Flat p] [Surjective p] [QuasiCompact p] {U U' : V.left.Opens}
    (hU : D.IsInvariant U) (hU' : D.IsInvariant U') (hle : U' ≤ U)
    (hE : (D.restrict U hU).IsEffective) : (D.restrict U' hU').IsEffective := by
  obtain ⟨V₀, q, hq, hinv⟩ := hE
  have : Flat q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq.flip inferInstance
  have hsat : q ⁻¹' (q '' (U.ι ⁻¹ᵁ U' : Set U.toScheme)) = (U.ι ⁻¹ᵁ U' : Set U.toScheme) := by
    refine subset_antisymm (fun w ⟨w', hw', e⟩ ↦ ?_) (Set.subset_preimage_image _ _)
    exact mem_of_apply_eq_apply hq hinv hU' e.symm hw'
  let O : V₀.left.Opens := ⟨q '' (U.ι ⁻¹ᵁ U' : Set U.toScheme),
    (Flat.isQuotientMap_of_surjective q).isOpen_preimage.mp (by
      rw [hsat]
      exact (U.ι ⁻¹ᵁ U').2)⟩
  have hO : q ⁻¹ᵁ O = U.ι ⁻¹ᵁ U' := TopologicalSpace.Opens.ext hsat
  have hr : Set.range (V.left.homOfLE hle ≫ q) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    refine ⟨V.left.homOfLE hle w, ?_, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply]
    rw [Scheme.homOfLE_ι]
    exact w.2
  let q' := IsOpenImmersion.lift O.ι (V.left.homOfLE hle ≫ q) hr
  have hq' : q' ≫ O.ι = V.left.homOfLE hle ≫ q := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.mk (O.ι ≫ V₀.hom), q', ?_, fun f₁ f₂ h a ↦ ?_⟩
  · have top : IsPullback q' (V.left.homOfLE hle) O.ι q :=
      IsOpenImmersion.isPullback _ _ _ _ hq'.symm (by
        rw [Scheme.Opens.opensRange_ι, Scheme.opensRange_homOfLE, hO])
    simpa using top.paste_vert hq
  · rw [← cancel_mono O.ι, Category.assoc, hq', Category.assoc, hq',
      restrict_transport_left_homOfLE_assoc hU hU' hle, hinv]
    rfl

namespace EffectiveGluing

variable (D) in
/-- The index set of the gluing: the invariant open subschemes of `V` on which `D` is effective,
ordered by inclusion. -/
abbrev Idx : Type u := {U : V.left.Opens // ∃ hU : D.IsInvariant U, (D.restrict U hU).IsEffective}

instance : PartialOrder (Idx D) := Subtype.partialOrder _

instance : Category (Idx D) := Preorder.smallCategory _

instance : Quiver.IsThin (Idx D) := fun _ _ ↦ inferInstanceAs (Subsingleton (ULift _))

lemma isInvariant (W : Idx D) : D.IsInvariant W.1 := W.2.1

/-- A chosen descent of the restriction of `D` to `W`. -/
noncomputable def obj (W : Idx D) : Over Y := W.2.2.choose

/-- The projection of `W` to its descent. -/
noncomputable def proj (W : Idx D) : W.1.toScheme ⟶ (obj W).left := W.2.2.choose_spec.choose

lemma isPullback_proj (W : Idx D) : IsPullback (proj W) (W.1.ι ≫ V.hom) (obj W).hom p :=
  W.2.2.choose_spec.choose_spec.1

@[reassoc]
lemma proj_transport (W : Idx D) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ Over.mk (W.1.ι ≫ V.hom)) :
    ((D.restrict W.1 (isInvariant W)).transport f₁ f₂ h a).left ≫ proj W = a.left ≫ proj W :=
  W.2.2.choose_spec.choose_spec.2 f₁ f₂ h a

variable [Flat p] [Surjective p] [QuasiCompact p]

instance (W : Idx D) : Flat (proj W) :=
  MorphismProperty.of_isPullback (isPullback_proj W).flip inferInstance

instance (W : Idx D) : Surjective (proj W) :=
  MorphismProperty.of_isPullback (isPullback_proj W).flip inferInstance

instance (W : Idx D) : QuasiCompact (proj W) :=
  MorphismProperty.of_isPullback (isPullback_proj W).flip inferInstance

lemma existsUnique_trans {W W' : Idx D} (hle : W.1 ≤ W'.1) :
    ∃! g : (obj W).left ⟶ (obj W').left, proj W ≫ g = V.left.homOfLE hle ≫ proj W' :=
  (D.restrict W.1 (isInvariant W)).existsUnique_desc_of_isPullback (isPullback_proj W)
    (proj_transport W) _ fun f₁ f₂ h a ↦ by
      rw [← Category.assoc, restrict_transport_left_homOfLE (isInvariant W') (isInvariant W) hle,
        proj_transport W']
      simp

/-- The transition map between the descents of `W ⊆ W'`. -/
noncomputable def trans {W W' : Idx D} (hle : W.1 ≤ W'.1) : (obj W).left ⟶ (obj W').left :=
  (existsUnique_trans hle).exists.choose

@[reassoc]
lemma proj_trans {W W' : Idx D} (hle : W.1 ≤ W'.1) :
    proj W ≫ trans hle = V.left.homOfLE hle ≫ proj W' :=
  (existsUnique_trans hle).exists.choose_spec

lemma trans_unique {W W' : Idx D} (hle : W.1 ≤ W'.1) (g : (obj W).left ⟶ (obj W').left)
    (hg : proj W ≫ g = V.left.homOfLE hle ≫ proj W') : g = trans hle :=
  (existsUnique_trans hle).unique hg (proj_trans hle)

@[reassoc (attr := simp)]
lemma trans_hom {W W' : Idx D} (hle : W.1 ≤ W'.1) : trans hle ≫ (obj W').hom = (obj W).hom := by
  rw [← cancel_epi (proj W), proj_trans_assoc, (isPullback_proj W').w, (isPullback_proj W).w]
  simp

/-- The diagram of the descents. -/
@[simps]
noncomputable def G : Idx D ⥤ Scheme.{u} where
  obj W := (obj W).left
  map g := trans (leOfHom g)
  map_id W := (trans_unique _ _ (by simp)).symm
  map_comp {W W' W''} g g' := (trans_unique _ _ (by
    rw [proj_trans_assoc, proj_trans, Scheme.homOfLE_homOfLE_assoc])).symm

lemma isPullback_trans {W W' : Idx D} (hle : W.1 ≤ W'.1) :
    IsPullback (V.left.homOfLE hle) (proj W) (proj W') (trans hle) := by
  refine (IsPullback.of_bot ?_ (proj_trans hle) (isPullback_proj W')).flip
  simpa using isPullback_proj W

instance {W W' : Idx D} (g : W ⟶ W') : IsOpenImmersion ((G (D := D)).map g) :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_trans (leOfHom g))
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

lemma trans_proj_apply {W W' : Idx D} (hle : W.1 ≤ W'.1) (w : W.1.toScheme) :
    trans hle (proj W w) = proj W' (V.left.homOfLE hle w) := by
  rw [← Scheme.Hom.comp_apply, proj_trans, Scheme.Hom.comp_apply]

/-- The intersection of two indices. -/
def inf (i j : Idx D) : Idx D :=
  ⟨i.1 ⊓ j.1, (isInvariant i).inf _ (isInvariant j),
    isEffective_restrict_of_le (isInvariant i) _ inf_le_left i.2.2⟩

lemma inf_le_left (i j : Idx D) : inf i j ≤ i := _root_.inf_le_left (a := i.1) (b := j.1)

lemma inf_le_right (i j : Idx D) : inf i j ≤ j := _root_.inf_le_right (a := i.1) (b := j.1)

instance isLocallyDirected : ((G (D := D)) ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj hx := by
    obtain ⟨wi, rfl⟩ := (proj i).surjective xi
    obtain ⟨wj, rfl⟩ := (proj j).surjective xj
    change trans _ (proj i wi) = trans _ (proj j wj) at hx
    rw [trans_proj_apply, trans_proj_apply] at hx
    have hwj : (V.left.homOfLE (leOfHom fi) wi).1 ∈ j.1 :=
      mem_of_apply_eq_apply (isPullback_proj k) (proj_transport k) (isInvariant j) hx
        (by simp)
    let w : (inf i j).1.toScheme := ⟨wi.1, wi.2, by simpa using hwj⟩
    refine ⟨inf i j, homOfLE (inf_le_left i j), homOfLE (inf_le_right i j), proj (inf i j) w,
      ?_, ?_⟩
    · change trans _ (proj _ w) = _
      rw [trans_proj_apply]
      congr 1
      exact Subtype.ext (by simp [w])
    · change trans _ (proj _ w) = _
      rw [trans_proj_apply]
      apply ((G (D := D)).map fj).isOpenEmbedding.injective
      change trans _ (proj _ _) = trans _ (proj _ _)
      rw [trans_proj_apply, trans_proj_apply, ← hx]
      congr 1
      exact Subtype.ext (by simp [w])

section Colimit

/-- The glued scheme. -/
noncomputable abbrev glued : Scheme.{u} := colimit (G (D := D))

/-- The structure morphism of the glued scheme. -/
noncomputable def gluedHom : glued (D := D) ⟶ Y :=
  colimit.desc _ { pt := Y, ι := { app W := (obj W).hom } }

@[reassoc (attr := simp)]
lemma ι_gluedHom (W : Idx D) : colimit.ι (G (D := D)) W ≫ gluedHom = (obj W).hom :=
  colimit.ι_desc _ _

/-- The map `W ⟶ glued ×_Y X`. -/
noncomputable def θW (W : Idx D) : W.1.toScheme ⟶ Limits.pullback (gluedHom (D := D)) p :=
  pullback.lift (proj W ≫ colimit.ι (G (D := D)) W) (W.1.ι ≫ V.hom)
    (by rw [Category.assoc, ι_gluedHom, (isPullback_proj W).w])

@[reassoc (attr := simp)]
lemma θW_fst (W : Idx D) : θW W ≫ pullback.fst gluedHom p = proj W ≫ colimit.ι (G (D := D)) W :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma θW_snd (W : Idx D) : θW W ≫ pullback.snd gluedHom p = W.1.ι ≫ V.hom :=
  pullback.lift_snd _ _ _

lemma isPullback_θW (W : Idx D) :
    IsPullback (θW W) (proj W) (pullback.fst gluedHom p) (colimit.ι (G (D := D)) W) := by
  refine IsPullback.of_right ?_ (θW_fst W) (IsPullback.of_hasPullback gluedHom p).flip
  simpa using (isPullback_proj W).flip

instance (W : Idx D) : IsOpenImmersion (θW W) :=
  MorphismProperty.of_isPullback (isPullback_θW W).flip inferInstance

lemma homOfLE_θW {W W' : Idx D} (hle : W.1 ≤ W'.1) : V.left.homOfLE hle ≫ θW W' = θW W := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, θW_fst, θW_fst, ← proj_trans_assoc hle]
    exact congrArg (proj W ≫ ·) (colimit.w (G (D := D)) (homOfLE hle))
  · simp

lemma θW_compat (i j : Idx D) :
    pullback.fst i.1.ι j.1.ι ≫ θW i = pullback.snd i.1.ι j.1.ι ≫ θW j := by
  have hr : Set.range (pullback.fst i.1.ι j.1.ι ≫ i.1.ι) ⊆ Set.range (inf i j).1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Opens.range_ι, pullback.condition]
      exact ⟨_, rfl⟩
  let π := IsOpenImmersion.lift (inf i j).1.ι (pullback.fst _ _ ≫ i.1.ι) hr
  have hπ : π ≫ (inf i j).1.ι = pullback.fst _ _ ≫ i.1.ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : pullback.fst i.1.ι j.1.ι = π ≫ V.left.homOfLE (inf_le_left i j) := by
    rw [← cancel_mono i.1.ι, Category.assoc, Scheme.homOfLE_ι, hπ]
  have h2 : pullback.snd i.1.ι j.1.ι = π ≫ V.left.homOfLE (inf_le_right i j) := by
    rw [← cancel_mono j.1.ι, Category.assoc, Scheme.homOfLE_ι, hπ, pullback.condition]
  rw [h1, h2, Category.assoc, Category.assoc, homOfLE_θW, homOfLE_θW]

end Colimit

section Glue

variable (h : ∀ v : V.left, ∃ W : Idx D, v ∈ W.1)

/-- The open cover of `V` by the indices. -/
noncomputable def cover : V.left.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx D) (fun W ↦ W.1.toScheme) (fun W ↦ W.1.ι) (fun v ↦ by
    obtain ⟨W, hW⟩ := h v
    exact ⟨W, ⟨v, hW⟩, rfl⟩)

/-- The comparison map `V ⟶ glued ×_Y X`, glued from the `θW`. -/
noncomputable def θ : V.left ⟶ Limits.pullback (gluedHom (D := D)) p :=
  (cover h).glueMorphisms θW θW_compat

@[reassoc (attr := simp)]
lemma ι_θ (W : Idx D) : W.1.ι ≫ θ h = θW W :=
  (cover h).ι_glueMorphisms θW θW_compat W

@[reassoc (attr := simp)]
lemma θ_snd : θ h ≫ pullback.snd gluedHom p = V.hom := by
  refine (cover h).hom_ext _ _ fun W ↦ ?_
  change W.1.ι ≫ θ h ≫ _ = W.1.ι ≫ V.hom
  rw [ι_θ_assoc, θW_snd]

lemma θ_apply (W : Idx D) (w : W.1.toScheme) : θ h w.1 = θW W w := by
  rw [← ι_θ h W, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]

lemma θ_injective : Function.Injective (θ h) := by
  intro u u' huu'
  obtain ⟨W, hW⟩ := h u
  obtain ⟨W', hW'⟩ := h u'
  have e := congrArg (pullback.fst gluedHom p) huu'
  rw [θ_apply h W ⟨u, hW⟩, θ_apply h W' ⟨u', hW'⟩, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, θW_fst, θW_fst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
  obtain ⟨l, g, g', y, hy, hy'⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (G (D := D))).mp e
  obtain ⟨z, rfl⟩ := (proj l).surjective y
  change trans _ (proj l z) = _ at hy
  change trans _ (proj l z) = _ at hy'
  rw [trans_proj_apply] at hy hy'
  have hul : u ∈ l.1 := mem_of_apply_eq_apply (isPullback_proj W) (proj_transport W)
    (isInvariant l) hy.symm (by simp)
  have hul' : u' ∈ l.1 := mem_of_apply_eq_apply (isPullback_proj W') (proj_transport W')
    (isInvariant l) hy'.symm (by simp)
  rw [θ_apply h l ⟨u, hul⟩, θ_apply h l ⟨u', hul'⟩] at huu'
  exact congrArg Subtype.val ((θW l).isOpenEmbedding.injective huu')

lemma θ_surjective : Function.Surjective (θ h) := by
  intro z
  obtain ⟨W, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (G (D := D))
    (pullback.fst gluedHom p z)
  obtain ⟨t, ht₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.fst gluedHom p) (g := colimit.ι (G (D := D)) W) z x hx.symm
  refine ⟨((isPullback_θW W).isoPullback.inv ≫ W.1.ι) t, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, θ_apply, ← Scheme.Hom.comp_apply,
    IsPullback.isoPullback_inv_fst, ht₁]

instance : IsLocalIso (θ h) where
  exists_isOpenImmersion v := by
    obtain ⟨W, hW⟩ := h v
    refine ⟨W.1, hW, ?_⟩
    rw [ι_θ h W]
    infer_instance

instance : IsOpenImmersion (θ h) :=
  IsOpenImmersion.of_isLocalIso_of_injective _ (θ_injective h)

instance : IsIso (θ h) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (by ext1; simpa using Set.range_eq_univ.mpr (θ_surjective h))

lemma univ_θ_fst :
    D.univ ≫ θ h ≫ pullback.fst gluedHom p =
      pullback.fst (V.hom ≫ p) p ≫ θ h ≫ pullback.fst gluedHom p := by
  let 𝒰 : (Limits.pullback (V.hom ≫ p) p).OpenCover :=
    Scheme.Cover.mkOfCovers (Idx D)
      (fun W ↦ (pullback.fst (V.hom ≫ p) p ⁻¹ᵁ W.1).toScheme)
      (fun W ↦ (pullback.fst (V.hom ≫ p) p ⁻¹ᵁ W.1).ι) (fun z ↦ by
        obtain ⟨W, hW⟩ := h (pullback.fst (V.hom ≫ p) p z)
        exact ⟨W, ⟨z, hW⟩, rfl⟩)
  refine 𝒰.hom_ext _ _ fun W ↦ ?_
  let O := pullback.fst (V.hom ≫ p) p ⁻¹ᵁ W.1
  change O.ι ≫ _ = O.ι ≫ _
  have hr : Set.range (O.ι ≫ pullback.fst (V.hom ≫ p) p) ⊆ Set.range W.1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact z.2
  let b : Over.mk (O.ι ≫ pullback.fst (V.hom ≫ p) p ≫ V.hom) ⟶ Over.mk (W.1.ι ≫ V.hom) :=
    Over.homMk (IsOpenImmersion.lift W.1.ι _ hr) (by simp)
  have hb : b.left ≫ W.1.ι = O.ι ≫ pullback.fst (V.hom ≫ p) p := IsOpenImmersion.lift_fac _ _ _
  have hp : (O.ι ≫ pullback.fst (V.hom ≫ p) p ≫ V.hom) ≫ p =
      (O.ι ≫ pullback.snd (V.hom ≫ p) p) ≫ p := by
    simp [pullback.condition]
  have ht : ((D.restrict W.1 (isInvariant W)).transport _ _ hp b).left ≫ W.1.ι = O.ι ≫ D.univ :=
    (restrict_transport_left_ι W.1 (isInvariant W) _ _ hp b).trans
      (D.transport_left_eq_comp O.ι _ _ (by rw [Category.assoc, pullback.condition])
        (Over.homMk (U := Over.mk (pullback.fst (V.hom ≫ p) p ≫ V.hom))
          (pullback.fst (V.hom ≫ p) p) rfl) hp rfl rfl _ hb)
  rw [← reassoc_of% ht, ι_θ_assoc, θW_fst, proj_transport_assoc, ← θW_fst, ← ι_θ_assoc h W,
    reassoc_of% hb]

end Glue

end EffectiveGluing

open EffectiveGluing in
/-- **Effectivity of descent data is local.** Let `p : X ⟶ Y` be faithfully flat and
quasi-compact, and let `D` be a descent datum on `V`. If every point of `V` has an invariant open
neighbourhood on which `D` is effective, then `D` is effective. -/
theorem isEffective_of_forall_exists_mem [Flat p] [Surjective p] [QuasiCompact p]
    (h : ∀ v : V.left, ∃ (U : V.left.Opens) (hU : D.IsInvariant U), v ∈ U ∧
      (D.restrict U hU).IsEffective) : D.IsEffective := by
  have h' (v : V.left) : ∃ W : Idx D, v ∈ W.1 := by
    obtain ⟨U, hU, hv, hE⟩ := h v
    exact ⟨⟨U, hU, hE⟩, hv⟩
  refine ⟨Over.mk gluedHom, θ h' ≫ pullback.fst gluedHom p,
    IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ (asIso (θ h')) rfl (θ_snd h'),
    fun f₁ f₂ hf a ↦ ?_⟩
  rw [D.transport_left_eq, Category.assoc, univ_θ_fst h', pullback.lift_fst_assoc]

end CategoryTheory.Over.DescentDatum
