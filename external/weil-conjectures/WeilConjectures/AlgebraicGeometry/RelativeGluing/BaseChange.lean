/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of relative spectra

Let `h : X' ⟶ X` be a morphism of schemes, `F` a quasi-coherent algebra on `X` and `F'` one on
`X'`, both given as presheaves of rings on the small affine Zariski sites with coequifibered
structure morphisms `α : 𝒪_X ⟶ F` and `α' : 𝒪_{X'} ⟶ F'`. A `PullbackData h α α'` provides,
for affine opens `U' ⊆ X'` and `U ⊆ X` with `U' ⊆ h⁻¹ U`, ring maps `F(U) → F'(U')` compatible
with the restrictions and the structure morphisms. Such data induces a comparison morphism
`Spec_{X'} F' ⟶ Spec_X F` over `h`, which is a pullback square as soon as `F'(U')` is the base
change `Γ(X', U') ⊗_{Γ(X, U)} F(U)` for enough pairs `(U', U)`.

## Main definitions

- `AlgebraicGeometry.Scheme.AffineZariskiSite.Pairs`: pairs `(U', U)` of affine opens with
  `U' ⊆ h⁻¹ U`.
- `AlgebraicGeometry.Scheme.AffineZariskiSite.pairsCover`: the locally directed open cover of
  `Spec_{X'} F'` by the charts `Spec F'(U')` indexed by such pairs.
- `AlgebraicGeometry.Scheme.AffineZariskiSite.PullbackData`: maps `F(U) → F'(U')` for pairs.
- `AlgebraicGeometry.Scheme.AffineZariskiSite.PullbackData.comparison`: the induced morphism
  `Spec_{X'} F' ⟶ Spec_X F`.

## Main statements

- `AlgebraicGeometry.Scheme.AffineZariskiSite.PullbackData.comparison_toBase`: the comparison
  morphism lies over `h`.
- `AlgebraicGeometry.Scheme.AffineZariskiSite.PullbackData.isPullback_comparison`: if the maps
  `F(U) → F'(U')` are base changes along `Γ(X, U) → Γ(X', U')` for a family of pairs covering
  `X'`, then `Spec_{X'} F' = X' ×_X Spec_X F`.
- `AlgebraicGeometry.Scheme.AffineZariskiSite.PullbackData.comparison_comp_relativeGluingMap`:
  compatibility of the comparison morphisms with the morphisms induced by maps of algebras.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X X' : Scheme.{u}} (h : X' ⟶ X)

/-- The pairs `(U', U)` of affine opens of `X'` and `X` with `U' ⊆ h⁻¹ U`, ordered
componentwise by the orders of the small affine Zariski sites. -/
def Pairs : Type u :=
  {q : X'.AffineZariskiSite × X.AffineZariskiSite // q.1.1 ≤ h ⁻¹ᵁ q.2.1}

/-- Pairs are ordered componentwise. -/
instance : Preorder (Pairs h) :=
  inferInstanceAs (Preorder {q : X'.AffineZariskiSite × X.AffineZariskiSite //
    q.1.1 ≤ h ⁻¹ᵁ q.2.1})

variable {h}

/-- The order on pairs is the componentwise order. -/
lemma Pairs.le_iff {q q' : Pairs h} : q ≤ q' ↔ q.1.1 ≤ q'.1.1 ∧ q.1.2 ≤ q'.1.2 :=
  Iff.rfl

variable (h) in
/-- Every point of `X'` lies in the first component of some pair. -/
lemma Pairs.exists_mem (x : X') : ∃ q : Pairs h, x ∈ q.1.1.1 := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show h x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show x ∈ h ⁻¹ᵁ U from hx)
  exact ⟨⟨(⟨W, hW⟩, ⟨U, hU⟩), hle⟩, hxW⟩

/-- The pairs are locally directed: two pairs whose first components contain `x` have a common
refinement whose first component contains `x`. -/
lemma Pairs.exists_le (q q' : Pairs h) (x : X') (hq : x ∈ q.1.1.1) (hq' : x ∈ q'.1.1.1) :
    ∃ k : Pairs h, k ≤ q ∧ k ≤ q' ∧ x ∈ k.1.1.1 := by
  obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter q.1.2.2 q'.1.2.2 (h x)
    ⟨q.2 hq, q'.2 hq'⟩
  obtain ⟨f', g', e', hf'⟩ := exists_basicOpen_le_affine_inter q.1.1.2 q'.1.1.2 x ⟨hq, hq'⟩
  obtain ⟨r, hr, hxr⟩ := (q.1.1.basicOpen f').2.exists_basicOpen_le
    (V := h ⁻¹ᵁ (q.1.2.basicOpen f).1) ⟨x, hf⟩ hf'
  refine ⟨⟨((q.1.1.basicOpen f').basicOpen r, q.1.2.basicOpen f), hr⟩,
    ⟨((q.1.1.basicOpen f').basicOpen_le r).trans (q.1.1.basicOpen_le f'), q.1.2.basicOpen_le f⟩,
    ⟨((q.1.1.basicOpen f').basicOpen_le r).trans ⟨g', e'.symm⟩, ⟨g, e.symm⟩⟩, hxr⟩

variable {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
  {F' : X'.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α' : (toOpensFunctor X').op ⋙ X'.presheaf ⟶ F'} (H' : α'.Coequifibered)

variable (h) in
/-- The open cover of the relative spectrum `Spec_{X'} F'` by the charts `Spec F'(U')`, indexed by
the pairs `(U', U)` with `U' ⊆ h⁻¹ U`. -/
@[simps I₀ X f]
noncomputable def pairsCover : (relativeGluingData H').glued.OpenCover where
  I₀ := Pairs h
  X q := (relativeGluingData H').functor.obj q.1.1
  f q := colimit.ι (relativeGluingData H').functor q.1.1
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun z ↦ ?_, fun q ↦ (relativeGluingData H').cover.map_prop q.1.1⟩
    obtain ⟨q, hq⟩ := Pairs.exists_mem h ((relativeGluingData H').toBase z)
    refine ⟨q, ?_⟩
    have hz : z ∈ (relativeGluingData H').toBase ⁻¹ᵁ q.1.1.1 := hq
    rw [toBase_preimage] at hz
    exact hz

/-- The indices of `pairsCover` are ordered as pairs. -/
instance : Preorder (pairsCover h H').I₀ :=
  inferInstanceAs (Preorder (Pairs h))

variable (h) in
/-- The cover `pairsCover` is locally directed, with transition maps the maps of charts. -/
@[reducible] noncomputable def pairsCoverLocallyDirected : (pairsCover h H').LocallyDirected where
  trans {q q'} f := (relativeGluingData H').functor.map (homOfLE (leOfHom f).1)
  trans_id q := by
    rw [show homOfLE (leOfHom (𝟙 q)).1 = 𝟙 q.1.1 from Subsingleton.elim _ _]
    exact (relativeGluingData H').functor.map_id _
  trans_comp {q q' q''} f f' := by
    rw [← Functor.map_comp]
    exact congrArg (relativeGluingData H').functor.map (Subsingleton.elim _ _)
  w f := colimit.w (relativeGluingData H').functor _
  directed {q q'} x := by
    set y := (pullback.fst (colimit.ι (relativeGluingData H').functor q.1.1)
      (colimit.ι (relativeGluingData H').functor q'.1.1) ≫
        colimit.ι (relativeGluingData H').functor q.1.1) x with hy
    have hmem (U : X'.AffineZariskiSite) (z) :
        (relativeGluingData H').toBase (colimit.ι (relativeGluingData H').functor U z) ∈ U.1 := by
      have : colimit.ι (relativeGluingData H').functor U z ∈
          (relativeGluingData H').toBase ⁻¹ᵁ U.1 := by
        rw [toBase_preimage]
        exact ⟨z, rfl⟩
      exact this
    have hyq : (relativeGluingData H').toBase y ∈ q.1.1.1 := by
      rw [hy, Scheme.Hom.comp_apply]
      exact hmem _ _
    have hyq' : (relativeGluingData H').toBase y ∈ q'.1.1.1 := by
      rw [hy, pullback.condition, Scheme.Hom.comp_apply]
      exact hmem _ _
    obtain ⟨k, hkq, hkq', hk⟩ := Pairs.exists_le q q' _ hyq hyq'
    have hyk : y ∈ (relativeGluingData H').toBase ⁻¹ᵁ k.1.1.1 := hk
    rw [toBase_preimage] at hyk
    obtain ⟨w, hw⟩ := hyk
    refine ⟨k, homOfLE hkq, homOfLE hkq', w, ?_⟩
    apply (pullback.fst (colimit.ι (relativeGluingData H').functor q.1.1)
      (colimit.ι (relativeGluingData H').functor q'.1.1) ≫
        colimit.ι (relativeGluingData H').functor q.1.1).isOpenEmbedding.injective
    have e : pullback.lift ((relativeGluingData H').functor.map (homOfLE hkq.1))
        ((relativeGluingData H').functor.map (homOfLE hkq'.1))
        (by rw [colimit.w, colimit.w]) ≫
        (pullback.fst (colimit.ι (relativeGluingData H').functor q.1.1)
          (colimit.ι (relativeGluingData H').functor q'.1.1) ≫
            colimit.ι (relativeGluingData H').functor q.1.1) =
          colimit.ι (relativeGluingData H').functor k.1.1 := by
      rw [pullback.lift_fst_assoc, colimit.w]
    have := congrArg (fun f ↦ f w) e
    simp only [Scheme.Hom.comp_apply] at this ⊢
    exact this.trans (hw.trans (by simp only [hy, Scheme.Hom.comp_apply]))
  property_trans f := inferInstance

variable (h) in
/-- Two morphisms out of the relative spectrum `Spec_{X'} F'` agree if they agree on the charts
`Spec F'(U')` for all affine opens `U'` with `U' ⊆ h⁻¹ U` for some affine open `U` of `X`. -/
lemma hom_ext_of_le_preimage {Y : Scheme.{u}} {f g : (relativeGluingData H').glued ⟶ Y}
    (hfg : ∀ (U' : X'.AffineZariskiSite) (U : X.AffineZariskiSite), U'.1 ≤ h ⁻¹ᵁ U.1 →
      colimit.ι (relativeGluingData H').functor U' ≫ f =
        colimit.ι (relativeGluingData H').functor U' ≫ g) : f = g :=
  (pairsCover h H').hom_ext _ _ fun q ↦ hfg q.1.1 q.1.2 q.2

variable (h α α') in
/-- An identification of `F'` with the pullback of `F` along `h : X' ⟶ X`, in the weak sense of
maps `F(U) → F'(U')` for affine opens `U' ⊆ h⁻¹ U`, compatible with the restriction maps and the
structure morphisms. -/
structure PullbackData where
  /-- The comparison maps `F(U) → F'(U')`. -/
  map {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    F.obj (op U) ⟶ F'.obj (op U')
  map_naturality {U'₁ U'₂ : X'.AffineZariskiSite} {U₁ U₂ : X.AffineZariskiSite}
    (i' : U'₁ ⟶ U'₂) (i : U₁ ⟶ U₂) (h₁ : U'₁.1 ≤ h ⁻¹ᵁ U₁.1) (h₂ : U'₂.1 ≤ h ⁻¹ᵁ U₂.1) :
    F.map i.op ≫ map h₁ = map h₂ ≫ F'.map i'.op
  app_comp_map {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    α.app (op U) ≫ map hU = h.appLE U.1 U'.1 hU ≫ α'.app (op U')

namespace PullbackData

variable (D : PullbackData h α α')

/-- The comparison morphism `Spec_{X'} F' ⟶ Spec_X F`, glued from the morphisms
`Spec F'(U') ⟶ Spec F(U)` over the pairs `(U', U)` with `U' ⊆ h⁻¹ U`. -/
noncomputable def comparison : (relativeGluingData H').glued ⟶ (relativeGluingData H).glued :=
  letI := pairsCoverLocallyDirected h H'
  (pairsCover h H').glueMorphismsOfLocallyDirected
    (fun q ↦ Spec.map (D.map q.2) ≫ colimit.ι (relativeGluingData H).functor q.1.2)
    fun {q q'} f ↦ by
      have hw : Spec.map (F.map (homOfLE (leOfHom f).2).op) ≫
          colimit.ι (relativeGluingData H).functor q'.1.2 =
            colimit.ι (relativeGluingData H).functor q.1.2 :=
        colimit.w (relativeGluingData H).functor (homOfLE (leOfHom f).2)
      have ht : (pairsCover h H').trans f = Spec.map (F'.map (homOfLE (leOfHom f).1).op) :=
        rfl
      rw [ht, ← Spec.map_comp_assoc, ← D.map_naturality (homOfLE (leOfHom f).1),
        Spec.map_comp_assoc, hw]

/-- On the chart `Spec F'(U')`, the comparison morphism is `Spec` of `F(U) → F'(U')` followed by
the chart `Spec F(U)`, for any `U` with `U' ⊆ h⁻¹ U`. -/
@[reassoc (attr := simp)]
lemma ι_comparison {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite}
    (hU : U'.1 ≤ h ⁻¹ᵁ U.1) :
    colimit.ι (relativeGluingData H').functor U' ≫ D.comparison H H' =
      Spec.map (D.map hU) ≫ colimit.ι (relativeGluingData H).functor U :=
  letI := pairsCoverLocallyDirected h H'
  (pairsCover h H').map_glueMorphismsOfLocallyDirected _ _ (⟨(U', U), hU⟩ : Pairs h)

/-- The comparison morphism lies over `h : X' ⟶ X`. -/
@[reassoc]
lemma comparison_toBase :
    D.comparison H H' ≫ (relativeGluingData H).toBase = (relativeGluingData H').toBase ≫ h :=
  hom_ext_of_le_preimage h H' fun U' U hU ↦ by
    rw [ι_comparison_assoc _ _ _ hU, ι_toBase, ι_toBase_assoc, ← Spec.map_comp_assoc,
      D.app_comp_map, Spec.map_comp_assoc, IsAffineOpen.SpecMap_appLE_fromSpec]

/-- The chart `Spec F'(U') ⟶ Spec F(U)` of the comparison morphism, composed with the
identifications `Spec Γ(U) ≅ U`, is a pullback square over `h.resLE U U'` whenever `F'(U')` is
the base change `Γ(X', U') ⊗_{Γ(X, U)} F(U)`. -/
lemma isPullback_natTrans_app {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite}
    (hU : U'.1 ≤ h ⁻¹ᵁ U.1)
    (hpush : IsPushout (h.appLE U.1 U'.1 hU) (α.app (op U)) (α'.app (op U')) (D.map hU)) :
    IsPullback ((relativeGluingData H').natTrans.app U') (Spec.map (D.map hU))
      (h.resLE U.1 U'.1 hU) ((relativeGluingData H).natTrans.app U) := by
  have T : IsPullback (U'.2.isoSpec.inv) (Spec.map (h.appLE U.1 U'.1 hU))
      (h.resLE U.1 U'.1 hU) U.2.isoSpec.inv := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
      Scheme.Hom.resLE_comp_ι, IsAffineOpen.isoSpec_inv_ι_assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).paste_horiz T

/-- **Base change of relative spectra.** If for a family of pairs `(U', U)` covering `X'` the map
`F(U) → F'(U')` exhibits `F'(U')` as the base change `Γ(X', U') ⊗_{Γ(X, U)} F(U)`, then the
comparison morphism exhibits `Spec_{X'} F'` as the fibre product `X' ×_X Spec_X F`. -/
theorem isPullback_comparison
    (hcov : ∀ x : X', ∃ (U' : X'.AffineZariskiSite) (U : X.AffineZariskiSite)
      (hU : U'.1 ≤ h ⁻¹ᵁ U.1), x ∈ U'.1 ∧
        IsPushout (h.appLE U.1 U'.1 hU) (α.app (op U)) (α'.app (op U')) (D.map hU)) :
    IsPullback (D.comparison H H') (relativeGluingData H').toBase (relativeGluingData H).toBase
      h := by
  choose U' U hU hx hpush using hcov
  refine IsPullback.flip <| Scheme.isPullback_of_openCover_of_isPullback _ _ _ _
    (X'.openCoverOfIsOpenCover (fun x ↦ (U' x).1) ?_)
    (fun x ↦ (relativeGluingData H').functor.obj (U' x))
    (fun x ↦ colimit.ι (relativeGluingData H').functor (U' x))
    (fun x ↦ (relativeGluingData H').natTrans.app (U' x))
    (fun x ↦ ((relativeGluingData H').isPullback_natTrans_ι_toBase (U' x)).flip) fun x ↦ ?_
  · refine TopologicalSpace.Opens.ext <| Set.eq_univ_of_forall fun x ↦ ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · have := (D.isPullback_natTrans_app H H' (hU x) (hpush x)).paste_vert
      ((relativeGluingData H).isPullback_natTrans_ι_toBase (U x))
    rwa [Scheme.Hom.resLE_comp_ι, ← ι_comparison] at this

end PullbackData

section Functoriality

variable {G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G} (HG : β.Coequifibered)
  {G' : X'.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {β' : (toOpensFunctor X').op ⋙ X'.presheaf ⟶ G'} (HG' : β'.Coequifibered)

/-- The comparison morphisms are compatible with the morphisms of relative spectra induced by
maps of quasi-coherent algebras `φ : F ⟶ G` and `φ' : F' ⟶ G'` which are compatible with the
base change data. -/
lemma PullbackData.comparison_comp_relativeGluingMap (D : PullbackData h α α')
    (E : PullbackData h β β') (φ : F ⟶ G) (φ' : F' ⟶ G')
    (hφ : ∀ {U' : X'.AffineZariskiSite} {U : X.AffineZariskiSite} (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      φ.app (op U) ≫ E.map hU = D.map hU ≫ φ'.app (op U')) :
    E.comparison HG HG' ≫ relativeGluingMap H HG φ =
      relativeGluingMap H' HG' φ' ≫ D.comparison H H' :=
  hom_ext_of_le_preimage h HG' fun U' U hU ↦ by
    rw [PullbackData.ι_comparison_assoc _ _ _ hU, ι_relativeGluingMap, ι_relativeGluingMap_assoc,
      PullbackData.ι_comparison _ _ _ hU, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hφ]

end Functoriality

end AlgebraicGeometry.Scheme.AffineZariskiSite
