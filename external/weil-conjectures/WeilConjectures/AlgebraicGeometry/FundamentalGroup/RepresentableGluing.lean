/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representable

/-!
# Representability of étale sheaves by finite étale schemes is Zariski local

Let `F` be a sheaf of sets on the small étale site of a scheme `Y`, and suppose that for every
affine open `U ⊆ Y` the restriction of `F` to étale `Y`-schemes over `U` is represented by a
finite étale `U`-scheme `X_U`. Then `F` is represented by a finite étale `Y`-scheme
(`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_forall_affineOpens`).

The `X_U` are canonically compatible: for `U ≤ U'`, the `U`-scheme `X_U` and the restriction of
`X_{U'}` to `U` represent the same functor, so the Yoneda lemma provides transition maps
`X_U ⟶ X_{U'}` with cartesian squares over `U ⟶ U'`. Mathlib's relative gluing along the
directed cover of `Y` by its affine opens (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`)
glues them to a finite étale `Y`-scheme `X`, and the sheaf property of `F` shows that `X`
represents `F`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}}

/-- An open subscheme of `Y` as an étale `Y`-scheme. -/
noncomputable abbrev openObj (U : Y.Opens) : Y.Etale := Etale.mk U.ι

/-- The inclusion of open subschemes as a morphism of étale `Y`-schemes. -/
noncomputable def openHom {U U' : Y.Opens} (h : U ≤ U') : openObj U ⟶ openObj U' :=
  homMk (Y.homOfLE h) (Y.homOfLE_ι h)

@[simp] lemma openHom_left {U U' : Y.Opens} (h : U ≤ U') : (openHom h).left = Y.homOfLE h := rfl

lemma openHom_refl (U : Y.Opens) : openHom (le_refl U) = 𝟙 _ :=
  EtaleTorsor.etaleHom_ext (by simp; rfl)

@[reassoc]
lemma openHom_comp {U U' U'' : Y.Opens} (h : U ≤ U') (h' : U' ≤ U'') :
    openHom h ≫ openHom h' = openHom (h.trans h') :=
  EtaleTorsor.etaleHom_ext (by simp)

section BasisCover

variable (𝔅 : Set Y.Opens) [h𝔅 : Fact (TopologicalSpace.Opens.IsBasis 𝔅)]

/-- The open cover of `Y` by the members of a basis `𝔅` of its topology. -/
@[simps I₀ X f]
noncomputable def basisCover : Y.OpenCover where
  I₀ := 𝔅
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ?_, inferInstance⟩
    obtain ⟨U, hU, hyU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp h𝔅.out
      (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨⟨U, hU⟩, by rw [Scheme.Opens.range_ι]; exact hyU⟩

instance : Preorder (basisCover 𝔅).I₀ := inferInstanceAs (Preorder 𝔅)

noncomputable instance : (basisCover 𝔅).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp) <| by
    have : (Set.range fun i : (basisCover 𝔅).I₀ ↦ ((basisCover 𝔅).f i).opensRange) = 𝔅 := by
      ext U
      simp only [basisCover_f, Scheme.Opens.opensRange_ι, Set.mem_range]
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun h ↦ ⟨⟨U, h⟩, rfl⟩⟩
    rw [this]
    exact h𝔅.out

lemma basisCover_trans {U V : 𝔅} (h : U ≤ V) :
    (basisCover 𝔅).trans (homOfLE h) = Y.homOfLE (show U.1 ≤ V.1 from h) :=
  rfl

end BasisCover

section Gluing

variable {𝔅 : Set Y.Opens} [h𝔅 : Fact (TopologicalSpace.Opens.IsBasis 𝔅)]
  (F : Sheaf Y.smallEtaleTopology (Type w)) (X : ∀ U : 𝔅, Over (openObj U.1))
  (r : ∀ U : 𝔅, ((Over.forget (openObj U.1)).op ⋙ F.obj).RepresentableBy (X U))

/-- The transition map `X_U ⟶ X_{U'}` for affine opens `U ≤ U'`: the morphism representing the
universal section over `X_U`. -/
noncomputable def τ {U U' : 𝔅} (h : U ≤ U') : (X U).left ⟶ (X U').left :=
  ((r U').exists_overElt_eq ((X U).hom ≫ openHom (show U.1 ≤ U'.1 from h))
    ((r U).overElt (𝟙 _))).choose

variable {F X r}

omit h𝔅 in
lemma τ_hom {U U' : 𝔅} (h : U ≤ U') :
    τ F X r h ≫ (X U').hom = (X U).hom ≫ openHom (show U.1 ≤ U'.1 from h) :=
  ((r U').exists_overElt_eq ((X U).hom ≫ openHom (show U.1 ≤ U'.1 from h))
    ((r U).overElt (𝟙 _))).choose_spec.1

omit h𝔅 in
lemma overElt_τ {U U' : 𝔅} (h : U ≤ U') :
    (r U').overElt (τ F X r h) = (r U).overElt (𝟙 _) :=
  ((r U').exists_overElt_eq ((X U).hom ≫ openHom (show U.1 ≤ U'.1 from h))
    ((r U).overElt (𝟙 _))).choose_spec.2

omit h𝔅 in
lemma overElt_comp_τ {U U' : 𝔅} (h : U ≤ U') {T : Y.Etale} (a : T ⟶ (X U).left) :
    (r U').overElt (a ≫ τ F X r h) = (r U).overElt a := by
  rw [(r U').overElt_comp, overElt_τ, ← (r U).overElt_comp, Category.comp_id]

omit h𝔅 in
lemma τ_refl (U : 𝔅) : τ F X r (le_refl U) = 𝟙 _ :=
  (r U).overElt_injective (by rw [τ_hom, openHom_refl, Category.comp_id, Category.id_comp])
    (by rw [overElt_τ])

omit h𝔅 in
lemma τ_comp {U U' U'' : 𝔅} (h : U ≤ U') (h' : U' ≤ U'') :
    τ F X r h ≫ τ F X r h' = τ F X r (h.trans h') :=
  (r U'').overElt_injective
    (by rw [Category.assoc, τ_hom, reassoc_of% τ_hom, openHom_comp, τ_hom])
    (by rw [overElt_comp_τ, overElt_τ, overElt_τ])

variable (F X r)

/-- The diagram of the `X_U` over the affine opens of `Y`. -/
noncomputable def gluingFunctor : 𝔅 ⥤ Scheme.{u} where
  obj U := (X U).left.left
  map h := (τ F X r (leOfHom h)).left
  map_id U := by
    rw [← id_left_eq]
    exact congr_arg (fun f ↦ f.left) (τ_refl (F := F) (X := X) (r := r) U)
  map_comp h h' := by
    rw [← comp_left_eq]
    exact congr_arg (fun f ↦ f.left)
      (τ_comp (F := F) (X := X) (r := r) (leOfHom h) (leOfHom h')).symm

/-- The structure maps `X_U ⟶ U`. -/
noncomputable def gluingNatTrans :
    gluingFunctor F X r ⟶ (basisCover 𝔅).functorOfLocallyDirected where
  app U := (X U).hom.left
  naturality U U' h := by
    have e : h = homOfLE (leOfHom h) := rfl
    change (τ F X r (leOfHom h)).left ≫ (X U').hom.left =
      (X U).hom.left ≫ (basisCover 𝔅).trans h
    rw [e, basisCover_trans]
    exact congr_arg (fun f ↦ f.left) (τ_hom (F := F) (X := X) (r := r) (leOfHom h))

lemma gluingNatTrans_equifibered : (gluingNatTrans F X r).Equifibered := by
  intro U U' h
  let hUU' : U.1 ≤ U'.1 := leOfHom h
  change IsPullback (τ F X r (leOfHom h)).left (X U).hom.left (X U').hom.left
    ((basisCover 𝔅).trans h)
  have e : h = homOfLE (leOfHom h) := rfl
  rw [e, basisCover_trans]
  have hτ : (τ F X r (leOfHom h)).left ≫ (X U').hom.left = (X U).hom.left ≫ Y.homOfLE hUU' :=
    congr_arg (fun f ↦ f.left) (τ_hom (F := F) (X := X) (r := r) (leOfHom h))
  -- the pullback `Q = X_{U'} ×_{U'} U`, as an étale `Y`-scheme over `U`
  let QC : Y.Etale := Etale.mk (pullback.snd (X U').hom.left (Y.homOfLE hUU') ≫ U.1.ι)
  let QO : Over (openObj U.1) := Over.mk (homMk (pullback.snd _ _) rfl : QC ⟶ openObj U.1)
  let fstC : QC ⟶ (X U').left := homMk (pullback.fst _ _) (by
    change _ = pullback.snd _ _ ≫ U.1.ι
    rw [← w_left (X U').hom, pullback.condition_assoc]
    exact congr_arg _ (Y.homOfLE_ι hUU'))
  let c : (X U).left ⟶ QC := homMk (pullback.lift _ _ hτ) (by
    change _ ≫ pullback.snd _ _ ≫ U.1.ι = _
    rw [pullback.lift_snd_assoc]
    exact w_left (X U).hom)
  obtain ⟨d, hd₁, hd₂⟩ := (r U).exists_overElt_eq QO.hom ((r U').overElt fstC)
  have hc₁ : c ≫ fstC = τ F X r (leOfHom h) := EtaleTorsor.etaleHom_ext (by simp [c, fstC])
  have hc₂ : c ≫ QO.hom = (X U).hom := EtaleTorsor.etaleHom_ext (by simp [c, QO])
  have hcd : c ≫ d = 𝟙 _ := (r U).overElt_injective
    (by rw [Category.assoc, hd₁, hc₂, Category.id_comp])
    (by rw [(r U).overElt_comp, hd₂, ← (r U').overElt_comp, hc₁, overElt_τ])
  have hdτ : d ≫ τ F X r (leOfHom h) = fstC := (r U').overElt_injective
    (by
      rw [Category.assoc, τ_hom, reassoc_of% hd₁]
      exact EtaleTorsor.etaleHom_ext (by simp [QO, fstC, pullback.condition]))
    (by rw [overElt_comp_τ, hd₂])
  have hdc : d ≫ c = 𝟙 _ := by
    refine EtaleTorsor.etaleHom_ext (pullback.hom_ext ?_ ?_)
    · have := congr_arg (fun f ↦ f.left) hdτ
      simpa [c, fstC] using this
    · have := congr_arg (fun f ↦ f.left) hd₁
      simpa [c, QO] using this
  refine IsPullback.of_iso_pullback ⟨hτ⟩ ⟨c.left, d.left, ?_, ?_⟩ (by simp [c]) (by simp [c])
  · rw [← comp_left_eq, hcd, id_left_eq]
  · rw [← comp_left_eq, hdc, id_left_eq]
    rfl

/-- The relative gluing datum of the `X_U` over the directed affine open cover of `Y`. -/
noncomputable def gluingData : (basisCover 𝔅).RelativeGluingData where
  functor := gluingFunctor F X r
  natTrans := gluingNatTrans F X r
  equifibered := gluingNatTrans_equifibered F X r

lemma gluingData_toBase_mem (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ U, P (X U).hom.left) : P (gluingData F X r).toBase := by
  refine IsZariskiLocalAtTarget.of_openCover (basisCover 𝔅) fun U ↦ ?_
  have h := ((gluingData F X r).isPullback_natTrans_ι_toBase U).flip
  change P (pullback.snd _ _)
  rw [← h.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact hP U

section Representation

variable {F X r}

/-- The structure morphism of an étale `Y`-scheme, with target `Y` (so that the directed affine
cover of `Y` can be pulled back along it). -/
abbrev structMap (T : Y.Etale) : T.left ⟶ Y := T.hom

/-- For an étale `Y`-scheme `T` and an affine open `U ⊆ Y`, the étale `Y`-scheme `T ×_Y U`. -/
noncomputable abbrev TU (T : Y.Etale) (U : 𝔅) : Y.Etale :=
  Etale.mk (pullback.fst (structMap T) U.1.ι ≫ T.hom)

/-- The open immersion `T ×_Y U ⟶ T`. -/
noncomputable def TUfst (T : Y.Etale) (U : 𝔅) : TU T U ⟶ T :=
  homMk (pullback.fst _ _) rfl

/-- The projection `T ×_Y U ⟶ U`. -/
noncomputable def TUsnd (T : Y.Etale) (U : 𝔅) : TU T U ⟶ openObj U.1 :=
  homMk (pullback.snd (structMap T) U.1.ι) pullback.condition.symm

omit h𝔅 in
@[simp] lemma TUfst_left (T : Y.Etale) (U : 𝔅) :
    (TUfst T U).left = pullback.fst (structMap T) U.1.ι := rfl
omit h𝔅 in
@[simp] lemma TUsnd_left (T : Y.Etale) (U : 𝔅) :
    (TUsnd T U).left = pullback.snd (structMap T) U.1.ι := rfl

lemma exists_mem_basis_le {y : Y} {V : Y.Opens} (hy : y ∈ V) :
    ∃ U : 𝔅, y ∈ U.1 ∧ U.1 ≤ V := by
  obtain ⟨U, hU, hyU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp h𝔅.out hy
  exact ⟨⟨U, hU⟩, hyU, hUV⟩

lemma mem_range_pullback_fst {T : Scheme.{u}} (f : T ⟶ Y) (U : Y.Opens) {t : T}
    (ht : f t ∈ U) : t ∈ Set.range (pullback.fst f U.ι) := by
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  exact ht

lemma iUnion_range_TUfst (T : Y.Etale) : ⋃ U : 𝔅, Set.range (TUfst T U).left = Set.univ := by
  refine Set.eq_univ_of_forall fun t ↦ ?_
  obtain ⟨U, hU, -⟩ := exists_mem_basis_le (𝔅 := 𝔅) (V := ⊤) (y := T.hom t) trivial
  exact Set.mem_iUnion.2 ⟨U, mem_range_pullback_fst (structMap T) U.1 hU⟩

/-- The transition maps of the pullback of the directed affine cover. -/
lemma pullback₁_trans (T : Y.Etale) {i j : 𝔅} (hij : i ⟶ j) :
    Cover.trans ((basisCover 𝔅).pullback₁ (structMap T)) hij =
      pullback.map (structMap T) i.1.ι (structMap T) j.1.ι (𝟙 _) (Y.homOfLE (leOfHom hij))
        (𝟙 _) (by simp) (by simp) :=
  rfl

variable (F X r) in
lemma exists_glue (T : Y.Etale) (s : F.obj.obj (op T)) :
    ∃ m : T.left ⟶ (gluingData F X r).glued, ∀ (U : 𝔅) (a : TU T U ⟶ (X U).left),
      a ≫ (X U).hom = TUsnd T U → (r U).overElt a = F.obj.map (TUfst T U).op s →
        pullback.fst (structMap T) U.1.ι ≫ m = a.left ≫ colimit.ι (gluingData F X r).functor U := by
  have H (U : 𝔅) : ∃ a : TU T U ⟶ (X U).left, a ≫ (X U).hom = TUsnd T U ∧
      (r U).overElt a = F.obj.map (TUfst T U).op s :=
    (r U).exists_overElt_eq (TUsnd T U) (F.obj.map (TUfst T U).op s)
  choose a ha₁ ha₂ using H
  let g (U : 𝔅) : pullback (structMap T) U.1.ι ⟶ (gluingData F X r).glued :=
    (a U).left ≫ colimit.ι (gluingData F X r).functor U
  have hg {i j : 𝔅} (hij : i ⟶ j) :
      Cover.trans ((basisCover 𝔅).pullback₁ (structMap T)) hij ≫ g j = g i := by
    let transC : TU T i ⟶ TU T j :=
      homMk (pullback.map _ _ _ _ (𝟙 _) (Y.homOfLE (leOfHom hij)) (𝟙 _) (by simp) (by simp))
        (by simp)
    have hfst : transC ≫ TUfst T j = TUfst T i := EtaleTorsor.etaleHom_ext (by simp [transC])
    have hsnd : transC ≫ TUsnd T j = TUsnd T i ≫ openHom (show i.1 ≤ j.1 from leOfHom hij) :=
      EtaleTorsor.etaleHom_ext (by simp [transC])
    have e : transC ≫ a j = a i ≫ τ F X r (leOfHom hij) := by
      refine (r j).overElt_injective ?_ ?_
      · rw [Category.assoc, ha₁, Category.assoc, τ_hom, reassoc_of% ha₁, hsnd]
      · have h₁ := (r j).overElt_comp transC (a j)
        have h₂ := overElt_comp_τ (F := F) (X := X) (r := r) (leOfHom hij) (a i)
        rw [h₁, h₂, ha₂, ha₂, ← Functor.map_comp_apply, ← op_comp, hfst]
    have e' : transC.left ≫ (a j).left = (a i).left ≫ (τ F X r (leOfHom hij)).left := by
      simpa using congr_arg (fun f ↦ f.left) e
    rw [pullback₁_trans]
    change transC.left ≫ (a j).left ≫ _ = _
    rw [reassoc_of% e']
    exact congr_arg _ (colimit.w (gluingData F X r).functor hij)
  refine ⟨OpenCover.glueMorphismsOfLocallyDirected ((basisCover 𝔅).pullback₁ (structMap T)) g hg,
    fun U a' ha'₁ ha'₂ ↦ ?_⟩
  have : a' = a U := (r U).overElt_injective (ha'₁.trans (ha₁ U).symm) (ha'₂.trans (ha₂ U).symm)
  subst this
  exact OpenCover.map_glueMorphismsOfLocallyDirected ((basisCover 𝔅).pullback₁ (structMap T)) g hg U

variable (F X r) in
/-- The morphism `T ⟶ X` to the glued scheme attached to a section of `F` over `T`. -/
noncomputable def glueLeft (T : Y.Etale) (s : F.obj.obj (op T)) :
    T.left ⟶ (gluingData F X r).glued :=
  (exists_glue F X r T s).choose

lemma fst_glueLeft (T : Y.Etale) (s : F.obj.obj (op T)) (U : 𝔅)
    (a : TU T U ⟶ (X U).left) (ha₁ : a ≫ (X U).hom = TUsnd T U)
    (ha₂ : (r U).overElt a = F.obj.map (TUfst T U).op s) :
    pullback.fst (structMap T) U.1.ι ≫ glueLeft F X r T s =
      a.left ≫ colimit.ι (gluingData F X r).functor U :=
  (exists_glue F X r T s).choose_spec U a ha₁ ha₂

lemma hom_ext_pullback₁ {T : Y.Etale} {Z : Scheme.{u}} {f₁ f₂ : T.left ⟶ Z}
    (h : ∀ U : 𝔅, pullback.fst (structMap T) U.1.ι ≫ f₁ = pullback.fst (structMap T) U.1.ι ≫ f₂) :
    f₁ = f₂ :=
  Cover.hom_ext ((basisCover 𝔅).pullback₁ (structMap T)) _ _ h

lemma glueLeft_toBase (T : Y.Etale) (s : F.obj.obj (op T)) :
    glueLeft F X r T s ≫ (gluingData F X r).toBase = T.hom := by
  refine hom_ext_pullback₁ (𝔅 := 𝔅) fun U ↦ ?_
  obtain ⟨a, ha₁, ha₂⟩ := (r U).exists_overElt_eq (TUsnd T U) (F.obj.map (TUfst T U).op s)
  rw [reassoc_of% fst_glueLeft T s U a ha₁ ha₂, Cover.RelativeGluingData.ι_toBase]
  have := congr_arg (fun f ↦ f.left) ha₁
  simp only [comp_left_eq, TUsnd_left] at this
  change a.left ≫ (X U).hom.left ≫ U.1.ι = _
  rw [reassoc_of% this, ← pullback.condition]

variable (F X r) in
instance etale_toBase : AlgebraicGeometry.Etale (gluingData F X r).toBase :=
  gluingData_toBase_mem F X r @AlgebraicGeometry.Etale fun _ ↦ inferInstance

variable (F X r) in
/-- The glued scheme, as an étale `Y`-scheme. -/
noncomputable abbrev XG : Y.Etale := Etale.mk (gluingData F X r).toBase

variable (F X r) in
/-- The morphism `T ⟶ X` of étale `Y`-schemes attached to a section of `F` over `T`. -/
noncomputable def glue (T : Y.Etale) (s : F.obj.obj (op T)) : T ⟶ XG F X r :=
  homMk (glueLeft F X r T s) (glueLeft_toBase T s)

@[simp] lemma glue_left (T : Y.Etale) (s : F.obj.obj (op T)) :
    (glue F X r T s).left = glueLeft F X r T s := rfl

lemma glue_naturality {T T' : Y.Etale} (h : T' ⟶ T) (s : F.obj.obj (op T)) :
    glue F X r T' (F.obj.map h.op s) = h ≫ glue F X r T s := by
  refine EtaleTorsor.etaleHom_ext (hom_ext_pullback₁ (𝔅 := 𝔅) fun U ↦ ?_)
  obtain ⟨a, ha₁, ha₂⟩ := (r U).exists_overElt_eq (TUsnd T U) (F.obj.map (TUfst T U).op s)
  let hU : TU T' U ⟶ TU T U := homMk (pullback.map _ _ _ _ h.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, w_left]) (by simp)) (by
      change _ ≫ pullback.fst _ _ ≫ T.hom = pullback.fst _ _ ≫ T'.hom
      rw [pullback.lift_fst_assoc, Category.assoc, w_left])
  have h₁ : hU ≫ TUsnd T U = TUsnd T' U := EtaleTorsor.etaleHom_ext (by simp [hU])
  have h₂ : hU ≫ TUfst T U = TUfst T' U ≫ h := EtaleTorsor.etaleHom_ext (by simp [hU])
  have h₂' : hU.left ≫ pullback.fst (structMap T) U.1.ι =
      pullback.fst (structMap T') U.1.ι ≫ h.left := by
    simpa using congr_arg (fun f ↦ f.left) h₂
  rw [glue_left, comp_left_eq, glue_left, fst_glueLeft T' _ U (hU ≫ a)
    (by rw [Category.assoc, ha₁, h₁])
    (by rw [(r U).overElt_comp, ha₂, ← Functor.map_comp_apply, ← op_comp, h₂, op_comp,
      Functor.map_comp_apply]), ← reassoc_of% h₂', fst_glueLeft T s U a ha₁ ha₂, comp_left_eq,
    Category.assoc]

lemma glue_injective (T : Y.Etale) : Function.Injective (glue F X r T) := by
  intro s s' hss'
  refine ext_of_isSheaf F (TUfst (𝔅 := 𝔅) T) (iUnion_range_TUfst T) fun U ↦ ?_
  obtain ⟨a, ha₁, ha₂⟩ := (r U).exists_overElt_eq (TUsnd T U) (F.obj.map (TUfst T U).op s)
  obtain ⟨a', ha'₁, ha'₂⟩ :=
    (r U).exists_overElt_eq (TUsnd T U) (F.obj.map (TUfst T U).op s')
  have e : a.left ≫ colimit.ι (gluingData F X r).functor U =
      a'.left ≫ colimit.ι (gluingData F X r).functor U := by
    rw [← fst_glueLeft T s U a ha₁ ha₂, ← fst_glueLeft T s' U a' ha'₁ ha'₂, ← glue_left,
      ← glue_left, hss']
  have : a = a' := EtaleTorsor.etaleHom_ext ((cancel_mono _).1 e)
  subst this
  exact ha₂.symm.trans ha'₂

/-- The restriction of a morphism `t : T ⟶ X` to `T ×_Y U` factors through `X_U`. -/
lemma exists_lift (T : Y.Etale) (U : 𝔅) (φ : T.left ⟶ (gluingData F X r).glued)
    (hφ : φ ≫ (gluingData F X r).toBase = T.hom) :
    ∃ b : TU T U ⟶ (X U).left, b ≫ (X U).hom = TUsnd T U ∧
      b.left ≫ colimit.ι (gluingData F X r).functor U = pullback.fst (structMap T) U.1.ι ≫ φ := by
  have hpb := (gluingData F X r).isPullback_natTrans_ι_toBase U
  have hw : pullback.snd (structMap T) U.1.ι ≫ (basisCover 𝔅).f U =
      (pullback.fst (structMap T) U.1.ι ≫ φ) ≫ (gluingData F X r).toBase := by
    rw [Category.assoc, hφ]
    exact pullback.condition.symm
  refine ⟨homMk (hpb.lift _ _ hw) ?_, EtaleTorsor.etaleHom_ext (hpb.lift_fst _ _ _),
    hpb.lift_snd _ _ _⟩
  rw [← w_left (X U).hom]
  change hpb.lift _ _ hw ≫ (gluingData F X r).natTrans.app U ≫ U.1.ι = _
  rw [hpb.lift_fst_assoc]
  exact pullback.condition.symm

lemma glue_surjective (T : Y.Etale) : Function.Surjective (glue F X r T) := by
  intro t
  have ht : t.left ≫ (gluingData F X r).toBase = T.hom := w_left t
  choose b hb₁ hb₂ using fun U ↦ exists_lift T U t.left ht
  obtain ⟨s, hs, -⟩ := existsUnique_of_isSheaf F (TUfst (𝔅 := 𝔅) T) (iUnion_range_TUfst T)
    (fun U ↦ (r U).overElt (b U)) (by
      intro i j Z gi gj hij
      change F.obj.map gi.op ((r i).overElt (b i)) = F.obj.map gj.op ((r j).overElt (b j))
      rw [← (r i).overElt_comp, ← (r j).overElt_comp]
      -- the composite `ψ : Z ⟶ T` lands in `i ∩ j`
      let ψ : Z ⟶ T := gi ≫ TUfst T i
      have hψ (k : 𝔅) (g : Z ⟶ TU T k) (hg : g ≫ TUfst T k = ψ) (z : Z.left) :
          Z.hom z ∈ k.1 := by
        have e : g.left ≫ pullback.snd (structMap T) k.1.ι ≫ k.1.ι = Z.hom := by
          rw [← pullback.condition, ← w_left ψ, ← hg]
          rfl
        rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        exact Subtype.prop _
      -- separatedness for the cover of `Z` by its parts over affine opens in `i ∩ j`
      let I := {U : 𝔅 // U ≤ i ∧ U ≤ j}
      refine ext_of_isSheaf F (fun U : I ↦ TUfst Z U.1) ?_ fun U ↦ ?_
      · refine Set.eq_univ_of_forall fun z ↦ ?_
        obtain ⟨U, hU, hUij⟩ := exists_mem_basis_le (𝔅 := 𝔅) (V := i.1 ⊓ j.1)
          ⟨hψ i gi rfl z, hψ j gj hij.symm z⟩
        exact Set.mem_iUnion.2 ⟨⟨U, fun x hx ↦ (hUij hx).1, fun x hx ↦ (hUij hx).2⟩,
          mem_range_pullback_fst (structMap Z) U.1 hU⟩
      · -- both sides are the section represented by the lift `c : Z ×_Y U ⟶ X_U`
        obtain ⟨U, hUi, hUj⟩ := U
        obtain ⟨c, hc₁, hc₂⟩ := exists_lift Z U (ψ.left ≫ t.left) (by
          rw [Category.assoc, ht, w_left])
        have hc (V : 𝔅) (hUV : U ≤ V) (g : Z ⟶ TU T V)
            (hg : g ≫ TUfst T V = ψ) : TUfst Z U ≫ g ≫ b V = c ≫ τ F X r hUV := by
          have hpb := (gluingData F X r).isPullback_natTrans_ι_toBase V
          refine EtaleTorsor.etaleHom_ext (hpb.hom_ext ?_ ?_)
          · rw [← cancel_mono ((basisCover 𝔅).f V)]
            have e₁ := congr_arg (fun f ↦ f.left) (τ_hom (F := F) (X := X) (r := r) hUV)
            have e₂ := congr_arg (fun f ↦ f.left) (hb₁ V)
            have e₃ := congr_arg (fun f ↦ f.left) hc₁
            have e₄ := congr_arg (fun f ↦ f.left) hg
            simp only [comp_left_eq, openHom_left, TUsnd_left, TUfst_left] at e₁ e₂ e₃ e₄
            change (TUfst Z U ≫ g ≫ b V).left ≫ (X V).hom.left ≫ V.1.ι =
              (c ≫ τ F X r hUV).left ≫ (X V).hom.left ≫ V.1.ι
            simp only [comp_left_eq, Category.assoc, TUfst_left]
            have e₅ : g.left ≫ pullback.fst (structMap T) V.1.ι ≫ T.hom = Z.hom := by
              rw [reassoc_of% e₄]
              exact w_left ψ
            calc pullback.fst (structMap Z) U.1.ι ≫ g.left ≫ (b V).left ≫ (X V).hom.left ≫
                  V.1.ι = pullback.fst (structMap Z) U.1.ι ≫ g.left ≫
                    pullback.snd (structMap T) V.1.ι ≫ V.1.ι := by rw [reassoc_of% e₂]
              _ = pullback.fst (structMap Z) U.1.ι ≫ g.left ≫
                    pullback.fst (structMap T) V.1.ι ≫ T.hom := by
                rw [← pullback.condition]
              _ = pullback.snd (structMap Z) U.1.ι ≫ U.1.ι := by
                rw [e₅]
                exact pullback.condition
              _ = c.left ≫ (τ F X r hUV).left ≫ (X V).hom.left ≫ V.1.ι := by
                rw [reassoc_of% e₁, Scheme.homOfLE_ι, reassoc_of% e₃]
          · have e₅ := congr_arg (fun f ↦ f.left) hg
            simp only [comp_left_eq, TUfst_left] at e₅
            change (TUfst Z U ≫ g ≫ b V).left ≫ colimit.ι (gluingData F X r).functor V =
              (c ≫ τ F X r hUV).left ≫ colimit.ι (gluingData F X r).functor V
            simp only [comp_left_eq, Category.assoc, TUfst_left]
            rw [hb₂, reassoc_of% e₅]
            change _ = c.left ≫ (gluingData F X r).functor.map (homOfLE hUV) ≫
              colimit.ι (gluingData F X r).functor V
            rw [colimit.w, hc₂]
        rw [← (r i).overElt_comp, ← (r j).overElt_comp, ← Category.assoc, ← Category.assoc,
          Category.assoc (TUfst Z U) gi, hc i hUi gi rfl, Category.assoc (TUfst Z U) gj,
          hc j hUj gj hij.symm, overElt_comp_τ, overElt_comp_τ])
  refine ⟨s, EtaleTorsor.etaleHom_ext (hom_ext_pullback₁ (𝔅 := 𝔅) fun U ↦ ?_)⟩
  rw [glue_left, fst_glueLeft T s U (b U) (hb₁ U) (hs U).symm, hb₂]

end Representation

end Gluing

/-- **Representability by finite étale schemes is Zariski local.** Let `F` be a sheaf of sets on
the small étale site of `Y` and `𝔅` a basis of the topology of `Y` such that for every `U ∈ 𝔅`
the restriction of `F` to étale `Y`-schemes over `U` is represented by a finite étale
`U`-scheme. Then `F` is represented by a finite étale `Y`-scheme. -/
theorem exists_representableBy_of_isBasis (F : Sheaf Y.smallEtaleTopology (Type w))
    (𝔅 : Set Y.Opens) (h𝔅 : TopologicalSpace.Opens.IsBasis 𝔅)
    (H : ∀ U : 𝔅, ∃ X : Over (openObj U.1), IsFinite X.hom.left ∧
      Nonempty (((Over.forget (openObj U.1)).op ⋙ F.obj).RepresentableBy X)) :
    ∃ X : Y.Etale, IsFinite X.hom ∧ Nonempty (F.obj.RepresentableBy X) := by
  have : Fact (TopologicalSpace.Opens.IsBasis 𝔅) := ⟨h𝔅⟩
  choose X hX r using H
  let r' U := (r U).some
  refine ⟨XG F X r', gluingData_toBase_mem F X r' @IsFinite hX, ⟨?_⟩⟩
  let e (T : Y.Etale) : F.obj.obj (op T) ≃ (T ⟶ XG F X r') :=
    Equiv.ofBijective _ ⟨glue_injective T, glue_surjective T⟩
  refine ⟨fun {T} ↦ (e T).symm, fun {T T'} f g ↦ ?_⟩
  apply (e T).injective
  rw [Equiv.apply_symm_apply]
  change _ = glue F X r' T (F.obj.map f.op _)
  rw [glue_naturality]
  congr 1
  exact ((e T').apply_symm_apply g).symm

end AlgebraicGeometry.Scheme.Etale
