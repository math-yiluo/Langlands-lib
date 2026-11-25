/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheafChart
public import WeilConjectures.AlgebraicGeometry.VectorBundle
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-!
# `Spec_X (Sym^• ℰ)` is a vector bundle for locally free `ℰ`

The coordinates of the chart `AlgebraicGeometry.Scheme.Modules.symSpecChart` over an affine open
`U` with a basis `b` of `Γ(ℰ, U)` are the sections `ι (b k)` of `Sym^• ℰ`
(`AlgebraicGeometry.Scheme.Modules.symSpecChart_hom_appTop_coord`). On a smaller affine open the
basis vectors of one chart are linear combinations of those of another one, so the coordinate
changes are linear, and `Spec_X (Sym^• ℰ) ⟶ X` is a vector bundle of rank `c`
(`AlgebraicGeometry.Scheme.Modules.isVectorBundle_symSpecProj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.AffineZariskiSite

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- The section `ι m` of `Sym^• ℰ` over the preimage of an affine open `U`, for `m ∈ Γ(ℰ, U)`. -/
noncomputable def symCoord (U : X.AffineZariskiSite) (m : Γ(F, U.1)) :
    Γ(F.symSpec, F.symSpecProj ⁻¹ᵁ U.1) :=
  (sectionsIso F.coequifibered_toSymPresheaf U).inv (SymmetricAlgebra.ι Γ(X, U.1) Γ(F, U.1) m)

lemma top_le_preimage_fst_symSpecProj (U : X.AffineZariskiSite) :
    ⊤ ≤ CategoryTheory.Limits.pullback.fst F.symSpecProj U.1.ι ⁻¹ᵁ F.symSpecProj ⁻¹ᵁ U.1 := by
  rw [← Scheme.Hom.comp_preimage, CategoryTheory.Limits.pullback.condition,
    Scheme.Hom.comp_preimage,
    Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

lemma fst_appLE_symSpecProj (U : X.AffineZariskiSite) :
    (CategoryTheory.Limits.pullback.fst F.symSpecProj U.1.ι).appLE _ ⊤
        (F.top_le_preimage_fst_symSpecProj U) =
      (colimit.ι (relativeGluingData F.coequifibered_toSymPresheaf).functor U).appLE
        _ ⊤ (top_le_preimage_toBase _ U) ≫
        ((relativeGluingData F.coequifibered_toSymPresheaf).isPullback_natTrans_ι_toBase
          U).flip.isoPullback.inv.appTop := by
  have hP := ((relativeGluingData F.coequifibered_toSymPresheaf).isPullback_natTrans_ι_toBase
    U).flip
  rw [Scheme.Hom.appLE_congr_hom hP.isoPullback_inv_fst.symm _ _ _ (by
      rw [hP.isoPullback_inv_fst]; exact F.top_le_preimage_fst_symSpecProj U),
    ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ (top_le_preimage_toBase _ U) (by simp)]
  congr 1
  simp [Scheme.Hom.appLE]

/-- The coordinates of the chart `symSpecChart` over `U` are the sections `ι (b k)`. -/
lemma symSpecChart_hom_appTop_coord {c : ℕ} (U : X.AffineZariskiSite)
    (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) (k : Fin c) :
    (F.symSpecChart U b).hom.appTop (AffineSpace.coord _ (ULift.up k)) =
      (CategoryTheory.Limits.pullback.fst F.symSpecProj U.1.ι).appLE _ ⊤
        (F.top_le_preimage_fst_symSpecProj U) (F.symCoord U (b k)) := by
  have e1 : ∀ y, (colimit.ι (relativeGluingData F.coequifibered_toSymPresheaf).functor
      U).appLE _ ⊤ (top_le_preimage_toBase _ U)
        ((sectionsIso F.coequifibered_toSymPresheaf U).inv y) =
          (Scheme.ΓSpecIso _).inv y := fun y ↦ by
    have e0 : (sectionsIso F.coequifibered_toSymPresheaf U).inv ≫
        (colimit.ι (relativeGluingData F.coequifibered_toSymPresheaf).functor
          U).appLE _ ⊤ (top_le_preimage_toBase _ U) = (Scheme.ΓSpecIso _).inv := by
      rw [Iso.inv_comp_eq, sectionsIso_hom, Category.assoc]
      erw [Iso.hom_inv_id, Category.comp_id]
    exact congr($e0 y)
  have hc : (F.symSpecChart U b).hom =
      ((relativeGluingData F.coequifibered_toSymPresheaf).isPullback_natTrans_ι_toBase
          U).flip.isoPullback.inv ≫ Spec.map (F.symChartRingHom U b) ≫
          (AffineSpace.SpecIso _ _).inv ≫ AffineSpace.map _ U.2.isoSpec.inv := rfl
  rw [fst_appLE_symSpecProj, CommRingCat.comp_apply, symCoord]
  erw [e1]
  rw [hc,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply,
    AffineSpace.map_appTop_coord]
  erw [AffineSpace.SpecIso_inv_appTop_coord]
  congr 1
  have := congr($(Scheme.ΓSpecIso_inv_naturality (F.symChartRingHom U b))
    (MvPolynomial.X (ULift.up k)))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
  refine this.symm.trans ?_
  congr 1
  change (SymmetricAlgebra.equivMvPolynomial (b.reindex Equiv.ulift.symm)).symm
    (MvPolynomial.X (ULift.up k)) = _
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  simp

omit [F.IsQuasicoherent] in
/-- On an affine open `W ⊆ U` the restrictions of a basis of `Γ(ℰ, U)` generate `Γ(ℰ, W)`. -/
lemma span_range_restrict_basis [F.IsQuasicoherent] {c : ℕ} (W U : X.affineOpens)
    (h : W.1 ≤ U.1) (b : Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)) :
    Submodule.span Γ(X, W.1) (Set.range fun l ↦ F.presheaf.map (homOfLE h).op (b l)) = ⊤ := by
  obtain ⟨c', hc, -, ht⟩ := quasiCoherent_affine_section_baseChange X F W U h
  refine eq_top_iff.2 fun x hx ↦ ?_
  clear hx
  obtain ⟨t, rfl⟩ := hc.2 x
  induction t using TensorProduct.inductionOn with
  | tmul m r =>
    rw [ht m r]
    refine Submodule.smul_mem _ r ?_
    have hm : m ∈ Submodule.span Γ(X, U.1) (Set.range b) := b.mem_span m
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨l, rfl⟩ := hm
      exact Submodule.subset_span ⟨l, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add m m' _ _ hm hm' => rw [map_add]; exact add_mem hm hm'
    | smul r' m _ hm => rw [F.map_smul]; exact Submodule.smul_mem _ _ hm
  | add t t' ht ht' => rw [map_add]; exact add_mem ht ht'

lemma symCoord_restrict {U W : X.AffineZariskiSite} (h : W ⟶ U) (hle : W.1 ≤ U.1)
    (m : Γ(F, U.1)) :
    F.symSpec.presheaf.map (homOfLE (F.symSpecProj.preimage_mono hle)).op (F.symCoord U m) =
      F.symCoord W (F.presheaf.map (homOfLE hle).op m) := by
  have h0 := congr($(sectionsIso_hom_naturality F.coequifibered_toSymPresheaf h)
    ((sectionsIso F.coequifibered_toSymPresheaf U).inv
      (SymmetricAlgebra.ι Γ(X, U.1) Γ(F, U.1) m)))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h0
  calc _ = (sectionsIso F.coequifibered_toSymPresheaf W).inv
        ((sectionsIso F.coequifibered_toSymPresheaf W).hom
          (F.symSpec.presheaf.map (homOfLE (F.symSpecProj.preimage_mono hle)).op
            (F.symCoord U m))) := (Iso.hom_inv_id_apply _ _).symm
    _ = _ := by
      erw [h0]
      exact congrArg _ (F.symMap_ι _ m)

lemma symSpecProj_app_eq (W : X.AffineZariskiSite) (r : Γ(X, W.1)) :
    F.symSpecProj.app W.1 r = (sectionsIso F.coequifibered_toSymPresheaf W).inv
      (algebraMap Γ(X, W.1) (SymmetricAlgebra Γ(X, W.1) Γ(F, W.1)) r) := by
  have := toBase_appLE_sectionsIso_hom F.coequifibered_toSymPresheaf W
  rw [← Iso.eq_comp_inv] at this
  rw [Scheme.Hom.app_eq_appLE]
  exact congr($this r)

/-- Two chart coordinates are related linearly over an affine open `W ⊆ U₁ ∩ U₂`. -/
lemma exists_symCoord_relation {c : ℕ} {U₁ U₂ W : X.AffineZariskiSite} (h₁ : W ⟶ U₁)
    (h₂ : W ⟶ U₂) (hle₁ : W.1 ≤ U₁.1) (hle₂ : W.1 ≤ U₂.1)
    (b₁ : Module.Basis (Fin c) Γ(X, U₁.1) Γ(F, U₁.1)) (m : Γ(F, U₂.1)) :
    ∃ β : Fin c → Γ(X, W.1),
      F.symSpec.presheaf.map (homOfLE (F.symSpecProj.preimage_mono hle₂)).op
          (F.symCoord U₂ m) =
        ∑ l, F.symSpecProj.app W.1 (β l) *
          F.symSpec.presheaf.map (homOfLE (F.symSpecProj.preimage_mono hle₁)).op
            (F.symCoord U₁ (b₁ l)) := by
  have hspan := F.span_range_restrict_basis ⟨W.1, W.2⟩ ⟨U₁.1, U₁.2⟩ hle₁ b₁
  have hmem : F.presheaf.map (homOfLE hle₂).op m ∈ Submodule.span Γ(X, W.1)
      (Set.range fun l ↦ F.presheaf.map (homOfLE hle₁).op (b₁ l)) := by
    rw [hspan]; trivial
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  refine ⟨β, ?_⟩
  rw [F.symCoord_restrict h₂ hle₂]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun l _ ↦ by
    rw [F.symCoord_restrict h₁ hle₁, symSpecProj_app_eq]).symm
  have key : SymmetricAlgebra.ι Γ(X, W.1) Γ(F, W.1) (F.presheaf.map (homOfLE hle₂).op m) =
      ∑ l, algebraMap Γ(X, W.1) (SymmetricAlgebra Γ(X, W.1) Γ(F, W.1)) (β l) *
        SymmetricAlgebra.ι Γ(X, W.1) Γ(F, W.1) (F.presheaf.map (homOfLE hle₁).op (b₁ l)) := by
    rw [← hβ, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    exact (LinearMap.map_smul _ _ _).trans (Algebra.smul_def _ _)
  exact (congrArg _ key).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun l _ ↦ map_mul _ _ _))

omit [F.IsQuasicoherent] in
/-- Pulling back sections along `f` after `g.appLE U ⊤`. -/
lemma appTop_appLE_apply' {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens)
    (e : ⊤ ≤ g ⁻¹ᵁ U) (x : Γ(C, U)) :
    f.appTop (g.appLE U ⊤ e x) = (f ≫ g).appLE U ⊤ (by
      rw [Scheme.Hom.comp_preimage]; exact le_top.trans (Scheme.Hom.preimage_mono _ e)) x := by
  rw [← CommRingCat.comp_apply]
  have : f.appTop = f.appLE ⊤ ⊤ (by simp) := by simp [Scheme.Hom.appLE]
  rw [this, Scheme.Hom.appLE_comp_appLE]

omit [F.IsQuasicoherent] in
/-- A linear relation `σ₂ = ∑ t^*(βₗ) σ₁ₗ` between sections of `N` over `t⁻¹ W` pulls back along
`F : T ⟶ N` to a linear relation over `s⁻¹ g⁻¹ W`, when `F ≫ t = s ≫ g`. -/
lemma appLE_relation' {c : ℕ} {T N P Y : Scheme.{u}} (F : T ⟶ N) (s : T ⟶ P) (g : P ⟶ Y)
    (t : N ⟶ Y) (hF : F ≫ t = s ≫ g) (W : Y.Opens) {U₁ U₂ : N.Opens} (hU₁ : t ⁻¹ᵁ W ≤ U₁)
    (hU₂ : t ⁻¹ᵁ W ≤ U₂) (σ₁ : Fin c → Γ(N, U₁)) (σ₂ : Γ(N, U₂)) (β : Fin c → Γ(Y, W))
    (h : N.presheaf.map (homOfLE hU₂).op σ₂ =
      ∑ l, t.app W (β l) * N.presheaf.map (homOfLE hU₁).op (σ₁ l))
    (e₁ : ⊤ ≤ F ⁻¹ᵁ U₁) (e₂ : ⊤ ≤ F ⁻¹ᵁ U₂) :
    T.presheaf.map (homOfLE (le_top : s ⁻¹ᵁ g ⁻¹ᵁ W ≤ ⊤)).op (F.appLE U₂ ⊤ e₂ σ₂) =
      ∑ l, s.app (g ⁻¹ᵁ W) (g.app W (β l)) *
        T.presheaf.map (homOfLE (le_top : s ⁻¹ᵁ g ⁻¹ᵁ W ≤ ⊤)).op (F.appLE U₁ ⊤ e₁ (σ₁ l)) := by
  have hV : s ⁻¹ᵁ g ⁻¹ᵁ W ≤ F ⁻¹ᵁ t ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hF]
  have hres (U : N.Opens) (hU : t ⁻¹ᵁ W ≤ U) (e : ⊤ ≤ F ⁻¹ᵁ U) (σ : Γ(N, U)) :
      T.presheaf.map (homOfLE (le_top : s ⁻¹ᵁ g ⁻¹ᵁ W ≤ ⊤)).op (F.appLE U ⊤ e σ) =
        F.appLE (t ⁻¹ᵁ W) _ hV (N.presheaf.map (homOfLE hU).op σ) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE]
  have hcoef (b : Γ(Y, W)) :
      F.appLE (t ⁻¹ᵁ W) _ hV (t.app W b) = s.app (g ⁻¹ᵁ W) (g.app W b) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appLE,
      Scheme.Hom.appLE_congr_hom hF _ _ _ (by rw [← hF, Scheme.Hom.comp_preimage]; exact hV),
      Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    simp [Scheme.Hom.appLE]
  rw [hres _ hU₂, h, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, hcoef, hres _ hU₁]

/-- The coordinate changes between two charts `symSpecChart` are linear, locally on the
overlap. -/
theorem symSpecChart_linear {c : ℕ} (U₁ : X.AffineZariskiSite)
    (b₁ : Module.Basis (Fin c) Γ(X, U₁.1) Γ(F, U₁.1)) (U₂ : X.AffineZariskiSite)
    (b₂ : Module.Basis (Fin c) Γ(X, U₂.1) Γ(F, U₂.1)) (k : Fin c)
    (y : ↥(CategoryTheory.Limits.pullback U₁.1.ι U₂.1.ι)) :
    ∃ (U : (CategoryTheory.Limits.pullback U₁.1.ι U₂.1.ι).Opens) (_ : y ∈ U)
      (a : Fin c → Γ(CategoryTheory.Limits.pullback U₁.1.ι U₂.1.ι, U)),
      (CategoryTheory.Limits.pullback F.symSpecProj
        (CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι ≫ U₁.1.ι)).presheaf.map
        (homOfLE le_top).op
        ((CategoryTheory.Limits.pullback.map F.symSpecProj
          (CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι ≫ U₁.1.ι) F.symSpecProj U₂.1.ι
          (𝟙 _) (CategoryTheory.Limits.pullback.snd U₁.1.ι U₂.1.ι) (𝟙 X) (by simp)
          (by simp [CategoryTheory.Limits.pullback.condition])).appTop
          ((F.symSpecChart U₂ b₂).hom.appTop (AffineSpace.coord _ (ULift.up k)))) =
      ∑ l, (CategoryTheory.Limits.pullback.snd F.symSpecProj
          (CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι ≫ U₁.1.ι)).app U (a l) *
        (CategoryTheory.Limits.pullback F.symSpecProj
          (CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι ≫ U₁.1.ι)).presheaf.map
          (homOfLE le_top).op
          ((CategoryTheory.Limits.pullback.map F.symSpecProj
            (CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι ≫ U₁.1.ι) F.symSpecProj U₁.1.ι
            (𝟙 _) (CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι) (𝟙 X) (by simp)
            (by simp)).appTop
            ((F.symSpecChart U₁ b₁).hom.appTop (AffineSpace.coord _ (ULift.up l)))) := by
  set g := CategoryTheory.Limits.pullback.fst U₁.1.ι U₂.1.ι ≫ U₁.1.ι with hg
  have hx₁ : g y ∈ U₁.1 := by
    rw [hg, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]; exact Subtype.prop _
  have hx₂ : g y ∈ U₂.1 := by
    rw [hg, CategoryTheory.Limits.pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Opens.ι_apply]
    exact Subtype.prop _
  obtain ⟨f, f', hff', hxf⟩ := exists_basicOpen_le_affine_inter (X := X) U₁.2 U₂.2 (g y)
    ⟨hx₁, hx₂⟩
  have hle₁ : (U₁.basicOpen f).1 ≤ U₁.1 := X.basicOpen_le f
  have hle₂ : (U₁.basicOpen f).1 ≤ U₂.1 := by
    change X.basicOpen f ≤ U₂.1
    rw [hff']; exact X.basicOpen_le f'
  obtain ⟨β, hβ⟩ := F.exists_symCoord_relation (homOfLE (U₁.basicOpen_le f))
    (homOfLE ⟨f', hff'.symm⟩) hle₁ hle₂ b₁ (b₂ k)
  refine ⟨g ⁻¹ᵁ (U₁.basicOpen f).1, hxf, fun l ↦ g.app _ (β l), ?_⟩
  have hF : CategoryTheory.Limits.pullback.fst F.symSpecProj g ≫ F.symSpecProj =
      CategoryTheory.Limits.pullback.snd _ _ ≫ g :=
    CategoryTheory.Limits.pullback.condition
  simp only [symSpecChart_hom_appTop_coord, appTop_appLE_apply']
  simp only [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.map,
    Category.comp_id]
  exact appLE_relation' _ (CategoryTheory.Limits.pullback.snd _ _) _ _ hF _ _ _ _ _ β hβ _ _

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

**`Spec_X (Sym^• ℰ)` is a vector bundle.** If `ℰ` is quasi-coherent and locally free of rank `c`
(every point has an affine neighbourhood `U` on which `Γ(ℰ, U)` has a basis indexed by
`Fin c`), then `Spec_X (Sym^• ℰ) ⟶ X` is a vector bundle of rank `c` with zero section defined by
the augmentation `Sym^• ℰ ⟶ 𝒪_X`. -/
theorem isVectorBundle_symSpecProj (c : ℕ)
    (hF : ∀ x : X, ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧
      Nonempty (Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1))) :
    Scheme.Hom.IsVectorBundle c F.symSpecProj F.symSpecZeroSection where
  zeroSection_comp := F.symSpecZeroSection_symSpecProj
  isClosedImmersion_zeroSection := inferInstance
  nonempty_atlas := ⟨{
    ι := Σ U : X.AffineZariskiSite, Module.Basis (Fin c) Γ(X, U.1) Γ(F, U.1)
    V := fun j ↦ j.1.1
    v := fun j ↦ j.1.1.ι
    isOpenImmersion := fun _ ↦ inferInstance
    exists_mem_range := fun x ↦ by
      obtain ⟨U, hx, ⟨b⟩⟩ := hF x
      exact ⟨⟨U, b⟩, by rw [Scheme.Opens.range_ι]; exact hx⟩
    chart := fun j ↦ F.symSpecChart j.1 j.2
    chart_hom_over := fun j ↦ F.symSpecChart_hom_over j.1 j.2
    zeroSection_chart := fun j ↦ F.exists_symSpecChart_zeroSection j.1 j.2
    linear := fun j₁ j₂ k y ↦ F.symSpecChart_linear j₁.1 j₁.2 j₂.1 j₂.2 k y }⟩

end AlgebraicGeometry.Scheme.Modules
