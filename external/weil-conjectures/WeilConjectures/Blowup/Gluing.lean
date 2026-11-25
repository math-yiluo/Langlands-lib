/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import WeilConjectures.Blowup.Affine.Localization
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-!

# The blow-up of a scheme along a quasi-coherent ideal

We construct the blow-up of a scheme `X` along a quasi-coherent ideal
`I : X.IdealSheafData` by relative gluing (`Scheme.Cover.RelativeGluingData`) of the affine
blow-ups `AffineBlowup (I.ideal U)` over the locally directed cover of all affine opens of
`X`. Since the index category is a thin preorder, no cocycle conditions appear; the gluing
obligation is that the local blow-ups form a functor whose structure maps are equifibered
over `X`, which we reduce to the localization theorem of
`WeilConjectures.Blowup.Affine.Localization`.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.blowupFunctor` — the diagram
  `U ↦ AffineBlowup (I.ideal U)` on the affine opens of `X`.
- `AlgebraicGeometry.Scheme.IdealSheafData.blowup` — the blow-up of `X` along `I`
  (blueprint: `def:nagata-global-blowup`).
- `AlgebraicGeometry.Scheme.IdealSheafData.blowupMap` — the structure morphism
  `I.blowup ⟶ X` (blueprint: `def:nagata-global-blowup-map`).
- `AlgebraicGeometry.Scheme.IdealSheafData.blowupι` — the chart embedding of the affine
  blow-up over an affine open.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowupι` — over an affine open `U`,
  the blow-up of `X` restricts to the affine blow-up of `U`
  (blueprint: `prop:nagata-global-blowup-affine-restrict`).

## Implementation notes

The blueprint's original roadmap glues over a chosen affine open cover with pairwise basic
overlap comparisons and explicit cocycle checks. We instead glue over the thin category of
all affine opens via `Scheme.Cover.RelativeGluingData`, which eliminates the cocycle
conditions; the overlap content is carried by the functoriality (`AffineBlowup.hom_comp`) and the
equifiberedness of the structure maps.

-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The diagram `U ↦ Bl_{I(U)} (Spec Γ(X, U))` over the affine opens of `X`.
(blueprint: `def:nagata-global-blowup-local-model`) -/
noncomputable def blowupFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := AffineBlowup (I.ideal U)
  map {U V} f :=
    AffineBlowup.hom (X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op).hom
      (I.map_ideal (leOfHom f))
  map_id U := by
    have e : (X.presheaf.map (homOfLE (X := X.Opens) (leOfHom (𝟙 U))).op).hom =
        RingHom.id Γ(X, U.1) := by
      rw [show homOfLE (X := X.Opens) (leOfHom (𝟙 U)) = 𝟙 U.1 from Subsingleton.elim _ _,
        op_id, X.presheaf.map_id, CommRingCat.hom_id]
    exact (AffineBlowup.hom_congr e _).trans AffineBlowup.hom_id
  map_comp {U V W} f g := by
    have e : (X.presheaf.map (homOfLE (X := X.Opens) (leOfHom (f ≫ g))).op).hom =
        ((X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op).hom).comp
          ((X.presheaf.map (homOfLE (X := X.Opens) (leOfHom g)).op).hom) := by
      rw [← CommRingCat.hom_comp, ← Functor.map_comp, ← op_comp,
        show homOfLE (X := X.Opens) (leOfHom f) ≫ homOfLE (X := X.Opens) (leOfHom g) =
          homOfLE (X := X.Opens) (leOfHom (f ≫ g)) from Subsingleton.elim _ _]
    exact (AffineBlowup.hom_congr e _).trans
      (AffineBlowup.hom_comp _ _ (I.map_ideal (leOfHom g)) (I.map_ideal (leOfHom f)))

@[simp]
lemma blowupFunctor_obj (U : X.affineOpens) :
    I.blowupFunctor.obj U = AffineBlowup (I.ideal U) :=
  rfl

lemma blowupFunctor_map {U V : X.affineOpens} (f : U ⟶ V) :
    I.blowupFunctor.map f =
      AffineBlowup.hom (X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op).hom
      (I.map_ideal (leOfHom f)) :=
  rfl

/-- The structure maps of the local blow-ups, as a natural transformation to the diagram of
affine opens of `X`. -/
noncomputable def blowupNatTrans :
    I.blowupFunctor ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app U := AffineBlowup.toSpec (I.ideal U) ≫ U.2.isoSpec.inv
  naturality {U V} f := by
    have hG : X.directedAffineCover.functorOfLocallyDirected.map f =
        X.homOfLE (leOfHom f) := rfl
    rw [hG, blowupFunctor_map, AffineBlowup.hom_toSpec_assoc, CommRingCat.ofHom_hom,
      specMap_res_isoSpec_inv (leOfHom f), Category.assoc]

lemma blowupNatTrans_app (U : X.affineOpens) :
    I.blowupNatTrans.app U = AffineBlowup.toSpec (I.ideal U) ≫ U.2.isoSpec.inv :=
  rfl

/-- Naturality of `blowupNatTrans` in terms of the inclusions of opens. -/
private lemma blowupNatTrans_naturality {U V : X.affineOpens} (hUV : U ≤ V) :
    I.blowupFunctor.map (homOfLE hUV) ≫ I.blowupNatTrans.app V =
      I.blowupNatTrans.app U ≫ X.homOfLE hUV :=
  I.blowupNatTrans.naturality (homOfLE hUV)

/-- Step A: the equifibered square for a basic-open inclusion of affine opens.
(blueprint: `def:nagata-global-blowup-overlap-basic-map`,
`lemma:nagata-global-blowup-overlap-basic`) -/
lemma isPullback_blowupNatTrans_of_basicOpen {U V : X.affineOpens} (hUV : U ≤ V)
    (f : Γ(X, V.1)) (hU : U.1 = X.basicOpen f) :
    IsPullback (I.blowupFunctor.map (homOfLE hUV)) (I.blowupNatTrans.app U)
      (I.blowupNatTrans.app V) (X.homOfLE hUV) := by
  let := (X.presheaf.map (homOfLE (X := X.Opens) hUV).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, U.1) :=
    V.2.isLocalization_of_eq_basicOpen f (homOfLE hUV) hU
  have halg : algebraMap Γ(X, V.1) Γ(X, U.1) =
      (X.presheaf.map (homOfLE (X := X.Opens) hUV).op).hom :=
    RingHom.algebraMap_toAlgebra _
  have hmap : ((I.ideal V).map (algebraMap Γ(X, V.1) Γ(X, U.1)) : Ideal Γ(X, U.1)) =
      I.ideal U := by
    rw [halg]; exact I.map_ideal hUV
  have key := AffineBlowup.isPullback_hom_of_isLocalization (B := Γ(X, U.1)) f hmap
  have w : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) Γ(X, U.1))) ≫
      V.2.isoSpec.inv = U.2.isoSpec.inv ≫ X.homOfLE hUV := by
    rw [halg, CommRingCat.ofHom_hom]
    exact specMap_res_isoSpec_inv hUV
  have e : I.blowupFunctor.map (homOfLE hUV) =
      AffineBlowup.hom (algebraMap Γ(X, V.1) Γ(X, U.1)) hmap :=
    (AffineBlowup.hom_congr halg hmap).symm
  rw [blowupNatTrans_app, blowupNatTrans_app, e]
  exact key.paste_vert (IsPullback.of_vert_isIso ⟨w⟩)

/-- Step B(i): the transition maps of the blow-up diagram are open immersions. -/
lemma isOpenImmersion_blowupFunctor_map {U V : X.affineOpens} (hUV : U ≤ V) :
    IsOpenImmersion (I.blowupFunctor.map (homOfLE hUV)) := by
  have H : ∀ i : {W : X.affineOpens // W ≤ U ∧ ∃ g : Γ(X, V.1), W.1 = X.basicOpen g},
      IsOpenImmersion (I.blowupFunctor.map (homOfLE (i.2.1.trans hUV))) := fun i ↦
    (I.isPullback_blowupNatTrans_of_basicOpen _ i.2.2.choose
      i.2.2.choose_spec).isOpenImmersion_fst
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion)
    (fun i : {W : X.affineOpens // W ≤ U ∧ ∃ g : Γ(X, V.1), W.1 = X.basicOpen g} ↦
      (I.blowupFunctor.map (homOfLE (i.2.1.trans hUV))).opensRange)
  · rintro _ ⟨z, rfl⟩
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    obtain ⟨g, hgU, hzg⟩ := V.2.exists_basicOpen_le (I.blowupNatTrans.app U z)
      (hUV (I.blowupNatTrans.app U z).2)
    have hWU : X.affineBasicOpen g ≤ U := hgU
    refine ⟨⟨X.affineBasicOpen g, hWU, g, rfl⟩, ?_⟩
    have hWgU : (X.affineBasicOpen g).1 =
        X.basicOpen ((X.presheaf.map (homOfLE (X := X.Opens) hUV).op) g) := by
      rw [X.basicOpen_res, inf_eq_right.mpr hgU]
      rfl
    have := (I.isPullback_blowupNatTrans_of_basicOpen hWU _ hWgU).isOpenImmersion_fst
    have hzW : z ∈ (I.blowupFunctor.map (homOfLE hWU)).opensRange := by
      rw [(I.isPullback_blowupNatTrans_of_basicOpen hWU _ hWgU).opensRange_fst,
        Scheme.Hom.mem_preimage, mem_opensRange_homOfLE]
      exact hzg
    obtain ⟨y, hy⟩ := hzW
    rw [← hy, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
      show homOfLE hWU ≫ homOfLE hUV = homOfLE (hWU.trans hUV) from Subsingleton.elim _ _]
    exact ⟨y, rfl⟩
  · intro i
    obtain ⟨g, hWg⟩ := i.2.2
    have hWgU : i.1.1 =
        X.basicOpen ((X.presheaf.map (homOfLE (X := X.Opens) hUV).op) g) := by
      rw [X.basicOpen_res, ← hWg, inf_eq_right.mpr (i.2.1 : i.1.1 ≤ U.1)]
    have h1 : IsOpenImmersion (I.blowupFunctor.map (homOfLE i.2.1)) :=
      (I.isPullback_blowupNatTrans_of_basicOpen i.2.1 _ hWgU).isOpenImmersion_fst
    have hcomp : homOfLE i.2.1 ≫ homOfLE hUV = homOfLE (i.2.1.trans hUV) :=
      Subsingleton.elim _ _
    have w : I.blowupFunctor.map (homOfLE i.2.1) ≫ I.blowupFunctor.map (homOfLE hUV) =
        𝟙 (I.blowupFunctor.obj i.1) ≫
          I.blowupFunctor.map (homOfLE (i.2.1.trans hUV)) := by
      rw [Category.id_comp, ← hcomp, Functor.map_comp]
    have hpre : I.blowupFunctor.map (homOfLE hUV) ⁻¹ᵁ
        (I.blowupFunctor.map (homOfLE (i.2.1.trans hUV))).opensRange =
        (I.blowupFunctor.map (homOfLE i.2.1)).opensRange := by
      rw [(I.isPullback_blowupNatTrans_of_basicOpen (i.2.1.trans hUV)
          i.2.2.choose i.2.2.choose_spec).opensRange_fst,
        (I.isPullback_blowupNatTrans_of_basicOpen i.2.1 _ hWgU).opensRange_fst,
        ← Scheme.Hom.comp_preimage, I.blowupNatTrans_naturality hUV,
        Scheme.Hom.comp_preimage,
        homOfLE_preimage_opensRange (i.2.1 : i.1.1 ≤ U.1) (hUV : U.1 ≤ V.1)]
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsOpenImmersion)
      (morphismRestrictArrowIso (I.blowupFunctor.map (homOfLE hUV)) (𝟙 _) w hpre)]
    infer_instance

instance {U V : X.affineOpens} (f : U ⟶ V) : IsOpenImmersion (I.blowupFunctor.map f) :=
  I.isOpenImmersion_blowupFunctor_map (leOfHom f)

/-- Step B(ii): the range of a transition map of the blow-up diagram is the preimage of the
corresponding open. -/
lemma opensRange_blowupFunctor_map {U V : X.affineOpens} (hUV : U ≤ V) :
    (I.blowupFunctor.map (homOfLE hUV)).opensRange =
      I.blowupNatTrans.app V ⁻¹ᵁ (X.homOfLE hUV).opensRange := by
  refine SetLike.ext fun z ↦ ?_
  constructor
  · rintro ⟨w, rfl⟩
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, I.blowupNatTrans_naturality hUV,
      Scheme.Hom.comp_apply]
    exact ⟨I.blowupNatTrans.app U w, rfl⟩
  · intro hz
    rw [Scheme.Hom.mem_preimage] at hz
    have hz1 : (I.blowupNatTrans.app V z).1 ∈ U.1 :=
      (mem_opensRange_homOfLE hUV _).mp hz
    obtain ⟨g, hgU, hzg⟩ := V.2.exists_basicOpen_le
      (⟨(I.blowupNatTrans.app V z).1, hz1⟩ : U.1) (I.blowupNatTrans.app V z).2
    have hWU : X.affineBasicOpen g ≤ U := hgU
    have hWV : X.affineBasicOpen g ≤ V := hWU.trans hUV
    have hb : (X.affineBasicOpen g).1 = X.basicOpen g := rfl
    have hzW : z ∈ (I.blowupFunctor.map (homOfLE hWV)).opensRange := by
      rw [(I.isPullback_blowupNatTrans_of_basicOpen hWV g hb).opensRange_fst,
        Scheme.Hom.mem_preimage]
      exact (mem_opensRange_homOfLE hWV _).mpr hzg
    obtain ⟨y, hy⟩ := hzW
    refine ⟨I.blowupFunctor.map (homOfLE hWU) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp,
      show homOfLE hWU ≫ homOfLE hUV = homOfLE hWV from Subsingleton.elim _ _]
    exact hy

/-- The structure maps of the local blow-ups are equifibered.
(blueprint: `lemma:nagata-global-blowup-glue-data-valid`) -/
lemma blowupNatTrans_equifibered : I.blowupNatTrans.Equifibered := by
  intro U V f
  exact (IsOpenImmersion.isPullback (I.blowupNatTrans.app U) (I.blowupFunctor.map f)
    (X.homOfLE (leOfHom f)) (I.blowupNatTrans.app V)
    (I.blowupNatTrans_naturality (leOfHom f))
    (I.opensRange_blowupFunctor_map (leOfHom f)).symm).flip

/-- The relative gluing datum for the blow-up of `X` along `I`.
(blueprint: `def:nagata-global-blowup-glue-data`) -/
noncomputable def blowupGluingData : X.directedAffineCover.RelativeGluingData where
  functor := I.blowupFunctor
  natTrans := I.blowupNatTrans
  equifibered := I.blowupNatTrans_equifibered

instance : (I.blowupFunctor ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs ((I.blowupGluingData.functor ⋙ Scheme.forget).IsLocallyDirected)

instance : Limits.HasColimit I.blowupFunctor :=
  inferInstanceAs (Limits.HasColimit I.blowupGluingData.functor)

/-- The blow-up of `X` along the quasi-coherent ideal `I`.
(blueprint: `def:nagata-global-blowup`) -/
noncomputable def blowup : Scheme.{u} :=
  I.blowupGluingData.glued

/-- The structure morphism of the blow-up.
(blueprint: `def:nagata-global-blowup-map`) -/
noncomputable def blowupMap : I.blowup ⟶ X :=
  I.blowupGluingData.toBase

/-- The chart embedding of the affine blow-up over an affine open into the blow-up.
(blueprint: `def:nagata-global-blowup`, chart embeddings) -/
noncomputable def blowupι (U : X.affineOpens) :
    AffineBlowup (I.ideal U) ⟶ I.blowup :=
  colimit.ι I.blowupFunctor U

instance (U : X.affineOpens) : IsOpenImmersion (I.blowupι U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι I.blowupFunctor U))

/-- The chart embeddings are compatible with the structure morphisms.
(blueprint: `lemma:nagata-global-blowup-local-maps-agree`,
`def:nagata-global-blowup-map` defining property) -/
@[reassoc (attr := simp)]
lemma blowupι_blowupMap (U : X.affineOpens) :
    I.blowupι U ≫ I.blowupMap = I.blowupNatTrans.app U ≫ U.1.ι :=
  I.blowupGluingData.ι_toBase U

/-- The preimage of an affine open under the blow-up map is the corresponding chart.
(blueprint: `def:nagata-global-blowup-affine-restriction-map`) -/
lemma blowupMap_preimage (U : X.affineOpens) :
    I.blowupMap ⁻¹ᵁ U.1 = (I.blowupι U).opensRange := by
  have h := I.blowupGluingData.toBase_preimage_eq_opensRange_ι U
  rwa [show (X.directedAffineCover.f U).opensRange = U.1 from
    Scheme.Opens.opensRange_ι U.1] at h

/-- **Affine restriction of the blow-up**: over an affine open `U`, the blow-up of `X`
restricts to the affine blow-up of `U`.
(blueprint: `prop:nagata-global-blowup-affine-restrict`) -/
theorem isPullback_blowupι (U : X.affineOpens) :
    IsPullback (I.blowupNatTrans.app U) (I.blowupι U) U.1.ι I.blowupMap :=
  I.blowupGluingData.isPullback_natTrans_ι_toBase U

/-- Transport of the blow-up structure morphism along an equality of centers. -/
lemma eqToHom_comp_blowupMap {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg blowup h) ≫ J.blowupMap = I.blowupMap := by
  subst h
  simp

end AlgebraicGeometry.Scheme.IdealSheafData
