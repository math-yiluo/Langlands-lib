/-
Sections `RestrictPkg`, `Main`, `Core` and `Main56` of the namespace
`Langlands.AlgebraicGeometry.FppfQuotientGluing` are adapted from
`P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean` and
`P2M/Sol/S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean` of
the Anthropic Lean formalization of Fermat's Last Theorem (commit
6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the
Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the finiteness hypotheses and conclusions are removed (the effective epimorphism
property comes from Mathlib's fppf instance instead of the fpqc one), the declarations are moved
to this namespace, and the gluing core and helper lemmas of the published port are imported
instead of copied. The paired Markdown file lists the changes.
-/
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpen
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict

/-! # Scheme quotients of étale equivalence relations by gluing affine quotients

Let `F` be an étale equivalence relation whose object scheme is covered by invariant opens
`V k` such that each restricted (chart) relation has an affine quotient. Then `F` has a scheme
quotient: a scheme `M` and an étale surjective `q : F.U ⟶ M` with `F.R = F.U ×_M F.U` via
`(F.t, F.s)`. The quotient is obtained by gluing the local quotients along the images of the
overlaps. This is the presentation form of the last step of Stacks Project, Lemma 70.5.11
(Tag 07SR): a space covered by open subspaces that are affine schemes is a scheme.

The gluing itself is the general statement
`FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict`: a relation
`s t : R ⟶ X` whose restrictions to the members of an invariant open cover have fppf quotients
(flat, locally of finite presentation, surjective, with the relation as kernel pair) has a global
such quotient. It is the Anthropic FLT result
`AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict` without its
finiteness hypotheses.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.FppfQuotientGluing

open _root_.AlgebraicGeometry.Scheme

open P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry.Scheme.GlueData
  (MkCore)
open P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry.Scheme.QuotGlue
  (preimage_image_eq imageOpens preimage_imageOpens imageOpens_top le_imageOpens_iff
    preimage_preimage_eq tRes tRes_ι tRes_ι_assoc sRes_w quotIso π_quotIso_hom
    π_quotIso_hom_assoc)
open scoped P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry.Scheme.GlueData.MkCore

section RestrictPkg

/-- Base change of an fppf quotient presentation along any morphism of the quotient: the base
changed morphism is again flat, locally of finite presentation and surjective, the base changed
relation is its kernel pair, and it is the coequalizer of that relation. -/
theorem quotient_baseChange {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by
  have : Flat p' := MorphismProperty.of_isPullback (P := @Flat) hX inferInstance
  have : LocallyOfFinitePresentation p' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hX inferInstance
  have : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hX inferInstance
  have hker : IsPullback s' t' p' p' := by
    refine IsPullback.of_isLimit' ⟨w'⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_)
      (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
    · refine hsq.lift (hR.lift (c.fst ≫ gX) (c.snd ≫ gX) ?_) c.fst ?_
      · rw [Category.assoc, Category.assoc, hX.w, ← Category.assoc, ← Category.assoc, c.condition]
      · rw [IsPullback.lift_fst]
    · exact hsq.lift_snd _ _ _
    · apply hX.hom_ext
      · rw [Category.assoc, ← htq, ← Category.assoc, hsq.lift_fst, hR.lift_snd]
      · rw [Category.assoc, ← w', ← Category.assoc, hsq.lift_snd, c.condition]
    · apply hsq.hom_ext
      · rw [hsq.lift_fst]
        apply hR.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, hsq.w, ← Category.assoc, hm₁]
        · rw [IsPullback.lift_snd, Category.assoc, htq, ← Category.assoc, hm₂]
      · rw [hsq.lift_snd]
        exact hm₁
  have hk : IsKernelPair p' s' t' := hker
  refine ⟨inferInstance, inferInstance, inferInstance, hker, ⟨?_⟩⟩
  exact hk.toCoequalizer (regularEpiOfEffectiveEpi p')

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

/-- Restriction of an fppf quotient presentation to an open of the quotient. -/
theorem restrict_pkg (hw : s ≫ p = t ≫ p) [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] (hR : IsPullback s t p p) (U : Y.Opens) :
    Flat (p ∣_ U) ∧ LocallyOfFinitePresentation (p ∣_ U) ∧
      Surjective (p ∣_ U) ∧ IsPullback (s ∣_ (p ⁻¹ᵁ U)) (tRes hw U) (p ∣_ U) (p ∣_ U) ∧
      Nonempty (IsColimit (Cofork.ofπ (p ∣_ U) (sRes_w hw U))) :=
  quotient_baseChange hR
    (isPullback_morphismRestrict p U).flip (isPullback_morphismRestrict s (p ⁻¹ᵁ U)).flip
    (tRes_ι hw U).symm (sRes_w hw U)

end RestrictPkg

section Main

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X → X.Opens) (hxW : ∀ x, x ∈ W x)
  (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)

noncomputable abbrev tW (x : X) : (s ⁻¹ᵁ W x : Scheme.{u}) ⟶ (W x : Scheme.{u}) :=
  (R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)

@[reassoc]
lemma tW_ι (x : X) : tW s t W hinv x ≫ (W x).ι = (s ⁻¹ᵁ W x).ι ≫ t := by
  rw [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

variable (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

noncomputable def Yloc (x : X) : Scheme.{u} := (loc x).choose

noncomputable def ploc (x : X) : (W x : Scheme.{u}) ⟶ Yloc s t W hinv loc x :=
  (loc x).choose_spec.choose
lemma ploc_spec (x : X) :
    (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x ∧
      Flat (ploc s t W hinv loc x) ∧
      LocallyOfFinitePresentation (ploc s t W hinv loc x) ∧ Surjective (ploc s t W hinv loc x) ∧
      IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (loc x).choose_spec.choose_spec

scoped instance (x : X) : Flat (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.1
scoped instance (x : X) : LocallyOfFinitePresentation (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.1
scoped instance (x : X) : Surjective (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.2.2.1

lemma inv_overlap (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) = (tW s t W hinv x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) := by
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = (tW s t W hinv x ≫ (W x).ι) ⁻¹ᵁ W y
  rw [morphismRestrict_ι, tW_ι]
  change (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (t ⁻¹ᵁ W y)
  rw [hinv y]

noncomputable def V (x y : X) : (Yloc s t W hinv loc x).Opens :=
  imageOpens (p := ploc s t W hinv loc x) ((W x).ι ⁻¹ᵁ W y)

lemma preimage_V (x y : X) : ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y = (W x).ι ⁻¹ᵁ W y :=
  preimage_imageOpens (ploc_spec s t W hinv loc x).2.2.2.2 _ (inv_overlap s t W hinv x y)

lemma range_overlap (x y : X) :
    Set.range ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) =
      (W x ⊓ W y : X.Opens) := by
  rw [preimage_V]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range, TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

variable {s t W hinv}

lemma hw (x : X) : (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x :=
  (ploc_spec s t W hinv loc x).1

lemma hpb (x : X) :
    IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.2

noncomputable abbrev pV (x y : X) := ploc s t W hinv loc x ∣_ V s t W hinv loc x y

noncomputable def coeqV (x y : X) :
    IsColimit (Cofork.ofπ (pV loc x y) (sRes_w (hw loc x) (V s t W hinv loc x y))) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.some

lemma isPullback_V (x y : X) :
    IsPullback ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
      (tRes (hw loc x) (V s t W hinv loc x y)) (pV loc x y) (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.1

noncomputable def eX (x y : X) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) ≅
      (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (W x).ι) (Scheme.Opens.ι _ ≫ (W y).ι)
    (by rw [range_overlap, range_overlap, inf_comm])

@[reassoc]
lemma eX_hom_ι (x y : X) :
    (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι = Scheme.Opens.ι _ ≫ (W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma sres_preimage (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y) := by
  rw [preimage_V]
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = _
  rw [morphismRestrict_ι]
  rfl

lemma range_roverlap (x y : X) :
    Set.range (((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)).ι ≫ (s ⁻¹ᵁ W x).ι) =
      (s ⁻¹ᵁ W x ⊓ s ⁻¹ᵁ W y : R.Opens) := by
  rw [sres_preimage]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range, TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

noncomputable def eR (x y : X) :
    ((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) : Scheme.{u}) ≅
      ((s ∣_ W y) ⁻¹ᵁ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x) : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι) (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι)
    (by rw [range_roverlap, range_roverlap, inf_comm])

@[reassoc]
lemma eR_hom_ι (x y : X) :
    (eR loc x y).hom ≫ Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι = Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma hs_comm (x y : X) :
    ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ ((s ∣_ W y) ∣_ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x)) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    morphismRestrict_ι_assoc, morphismRestrict_ι]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc, morphismRestrict_ι, eR_hom_ι_assoc]

lemma ht_comm (x y : X) :
    tRes (hw loc x) (V s t W hinv loc x y) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ tRes (hw loc y) (V s t W hinv loc y x) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    tRes_ι_assoc, tW_ι]
  simp only [Category.assoc]
  rw [tRes_ι_assoc, tW_ι, eR_hom_ι_assoc]

noncomputable def φ (x y : X) :
    (V s t W hinv loc x y : Scheme.{u}) ≅ (V s t W hinv loc y x : Scheme.{u}) :=
  quotIso (coeqV loc x y) (coeqV loc y x) (eR loc x y) (eX loc x y) (hs_comm loc x y) (ht_comm loc x y)

@[reassoc]
lemma pV_φ_hom (x y : X) : pV loc x y ≫ (φ loc x y).hom = (eX loc x y).hom ≫ pV loc y x :=
  π_quotIso_hom _ _ _ _ _ _

lemma V_self (x : X) : V s t W hinv loc x x = ⊤ := by
  rw [V, Scheme.Opens.ι_preimage_self]
  exact imageOpens_top

scoped instance epi_pV (x y : X) : Epi (pV loc x y) := by
  have h := restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)
  have : Flat (pV loc x y) := h.1
  have : LocallyOfFinitePresentation (pV loc x y) := h.2.1
  have : Surjective (pV loc x y) := h.2.2.1
  infer_instance

lemma eX_self (x : X) : (eX loc x x).hom = 𝟙 _ := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W x).ι), eX_hom_ι, Category.id_comp]

lemma φ_self (x : X) : (φ loc x x).hom = 𝟙 _ := by
  rw [← cancel_epi (pV loc x x), pV_φ_hom, eX_self, Category.id_comp, Category.comp_id]

end Main

section Core

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens}
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

scoped instance flat_pV (x y : X) : Flat (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).1
scoped instance lfp_pV (x y : X) : LocallyOfFinitePresentation (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.1
scoped instance surj_pV (x y : X) : Surjective (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.1

scoped instance epi_pV_restrict (x y : X) (O : (V s t W hinv loc x y : Scheme.{u}).Opens) :
    Epi (pV loc x y ∣_ O) := by
  have h := restrict_pkg (sRes_w (hw loc x) (V s t W hinv loc x y)) (isPullback_V loc x y) O
  have : Flat (pV loc x y ∣_ O) := h.1
  have : LocallyOfFinitePresentation (pV loc x y ∣_ O) := h.2.1
  have : Surjective (pV loc x y ∣_ O) := h.2.2.1
  infer_instance

lemma ι_mem_preimage_V {x y z : X} (u : ↑(ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
    (hu : ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ ploc s t W hinv loc x) u ∈
      V s t W hinv loc x z) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z :=
  hu

lemma core_t_inter (x y z : X) :
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) ≤
      (φ loc x y).hom ⁻¹ᵁ ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) := by
  intro v hv
  obtain ⟨u, rfl⟩ := (pV loc x y).surjective v

  have hv' : ((pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈ V s t W hinv loc x z := hv
  rw [morphismRestrict_ι] at hv'
  have hu : (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := hv'
  rw [preimage_V] at hu

  change ((pV loc x y ≫ (φ loc x y).hom) ≫ (V s t W hinv loc y x).ι) u ∈ V s t W hinv loc y z
  rw [pV_φ_hom, Category.assoc, morphismRestrict_ι]
  change ploc s t W hinv loc y (((eX loc x y).hom ≫ Scheme.Opens.ι _) u) ∈
    imageOpens (p := ploc s t W hinv loc y) ((W y).ι ⁻¹ᵁ W z)
  refine le_imageOpens_iff _ _ ?_
  change (((eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
  rw [eX_hom_ι]
  exact hu

lemma core_cocycle (x y z : X) :
    ((φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z))
        ((V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z)) (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫
        ((V s t W hinv loc y z).ι ⁻¹ᵁ (V s t W hinv loc y x)).ι ≫
          (φ loc y z).hom ≫ (V s t W hinv loc z y).ι) =
    ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
        (V s t W hinv loc x z)).hom ≫
      ((V s t W hinv loc x z).ι ⁻¹ᵁ (V s t W hinv loc x y)).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι := by

  set O : (V s t W hinv loc x y : Scheme.{u}).Opens :=
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) with hO
  rw [← cancel_epi (pV loc x y ∣_ O)]
  have hQ : (pV loc x y ∣_ O) ≫ O.ι = (pV loc x y ⁻¹ᵁ O).ι ≫ pV loc x y := morphismRestrict_ι _ _

  have hmem : ∀ u : ↑(pV loc x y ⁻¹ᵁ O),
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι) u ∈
        ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := by
    intro u
    have h1 : (pV loc x y ⁻¹ᵁ O).ι u ∈ ((pV loc x y ⁻¹ᵁ O : (_ : Scheme.{u}).Opens) : Set _) :=
      (Scheme.Opens.range_ι _).le ⟨u, rfl⟩
    have h2 : (((pV loc x y ⁻¹ᵁ O).ι ≫ pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈
        V s t W hinv loc x z := h1
    rw [morphismRestrict_ι] at h2
    exact h2
  have hmemW : ∀ u : ↑(pV loc x y ⁻¹ᵁ O),
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) u ∈
        W z := by
    intro u
    have := hmem u
    rw [preimage_V] at this
    exact this

  let lam₁ : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z) :=
    IsOpenImmersion.lift (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmem u)
  have hlam₁ : lam₁ ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let kap : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (W z : Scheme.{u}) :=
    IsOpenImmersion.lift (W z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmemW u)
  have hkap : kap ≫ (W z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let lam₂ : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z) :=
    IsOpenImmersion.lift (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫
        (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        change _ ∈ ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z
        rw [preimage_V]
        change (((pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
        rw [eX_hom_ι]
        exact hmemW u)
  have hlam₂ : lam₂ ≫ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫
        (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x).ι :=
    IsOpenImmersion.lift_fac _ _ _

  have σx : ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι ≫
        (V s t W hinv loc x z).ι = O.ι ≫ (V s t W hinv loc x y).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have σy : ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
      (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι ≫
        (V s t W hinv loc y z).ι =
      ((V s t W hinv loc y x).ι ⁻¹ᵁ V s t W hinv loc y z).ι ≫ (V s t W hinv loc y x).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

  have R1 : (pV loc x y ∣_ O) ≫ ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι =
      lam₁ ≫ pV loc x z := by
    rw [← cancel_mono (V s t W hinv loc x z).ι]
    simp only [Category.assoc]
    rw [σx, reassoc_of% hQ, morphismRestrict_ι (ploc s t W hinv loc x) (V s t W hinv loc x y),
      morphismRestrict_ι (ploc s t W hinv loc x) (V s t W hinv loc x z), reassoc_of% hlam₁]
  have R3 : lam₁ ≫ (eX loc x z).hom ≫ (ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [eX_hom_ι, reassoc_of% hlam₁, hkap]
  have R : (pV loc x y ∣_ O) ≫ ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι = kap ≫ ploc s t W hinv loc z := by
    rw [reassoc_of% R1, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc z) (V s t W hinv loc z x), reassoc_of% R3]

  have L1 : (pV loc x y ∣_ O) ≫
      (φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) O
        (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι =
      lam₂ ≫ pV loc y z := by
    rw [← cancel_mono (V s t W hinv loc y z).ι]
    simp only [Category.assoc]
    rw [σy, Scheme.Hom.resLE_comp_ι_assoc, reassoc_of% hQ, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc y) (V s t W hinv loc y x),
      morphismRestrict_ι (ploc s t W hinv loc y) (V s t W hinv loc y z), reassoc_of% hlam₂]
  have L3 : lam₂ ≫ (eX loc y z).hom ≫ (ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z y).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [eX_hom_ι, reassoc_of% hlam₂, eX_hom_ι, hkap]
  have L : (pV loc x y ∣_ O) ≫
      (φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) O
        (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι ≫
        (φ loc y z).hom ≫ (V s t W hinv loc z y).ι = kap ≫ ploc s t W hinv loc z := by
    rw [reassoc_of% L1, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc z) (V s t W hinv loc z y), reassoc_of% L3]
  rw [L, R]

noncomputable def core : MkCore.{u} where
  U := Yloc s t W hinv loc
  V := V s t W hinv loc
  t x y := (φ loc x y).hom
  V_id := V_self loc
  t_id := φ_self loc
  t_inter := core_t_inter loc
  cocycle := core_cocycle loc

@[scoped simp] lemma core_J : (core loc).J = X := rfl
@[scoped simp] lemma core_U (x : X) : (core loc).U x = Yloc s t W hinv loc x := rfl
@[scoped simp] lemma core_V (x y : X) : (core loc).V x y = V s t W hinv loc x y := rfl
@[scoped simp] lemma core_t (x y : X) : (core loc).t x y = (φ loc x y).hom := rfl

end Core

section Main56

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens} (hxW : ∀ x, x ∈ W x)
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

noncomputable abbrev D := (core loc).glueData

noncomputable def coverW : X.OpenCover :=
  Scheme.Cover.mkOfCovers X (fun x => (W x : Scheme.{u})) (fun x => (W x).ι)
    (fun x => ⟨x, ⟨x, hxW x⟩, rfl⟩)

@[scoped simp] lemma coverW_f (x : X) : (coverW hxW).f x = (W x).ι := rfl

noncomputable abbrev chart (x : X) : (W x : Scheme.{u}) ⟶ (D loc).glued :=
  ploc s t W hinv loc x ≫ (D loc).ι x

noncomputable def liftOverlap {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    T ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) :=
  IsOpenImmersion.lift (Scheme.Opens.ι _) a (by
    rw [Scheme.Opens.range_ι, preimage_V]
    rintro _ ⟨z, rfl⟩
    exact ha ⟨z, rfl⟩)

@[reassoc (attr := simp)]
lemma liftOverlap_ι {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    liftOverlap loc x y a ha ≫ Scheme.Opens.ι _ = a :=
  IsOpenImmersion.lift_fac _ _ _

lemma chart_comp_eq {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (b : T ⟶ (W y : Scheme.{u})) (hab : a ≫ (W x).ι = b ≫ (W y).ι) :
    a ≫ chart loc x = b ≫ chart loc y := by
  have ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X) := by
    rw [hab]; rintro _ ⟨z, rfl⟩; exact (b z).2
  have hb : Set.range (b ≫ (W y).ι) ⊆ (W x : Set X) := by
    rw [← hab]; rintro _ ⟨z, rfl⟩; exact (a z).2
  let a' := liftOverlap loc x y a ha
  let b' := liftOverlap loc y x b hb
  have hab' : a' ≫ (eX loc x y).hom = b' := by
    rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
      liftOverlap_ι_assoc, liftOverlap_ι_assoc, hab]
  calc a ≫ chart loc x
      = a' ≫ Scheme.Opens.ι _ ≫ ploc s t W hinv loc x ≫ (D loc).ι x := by
        rw [liftOverlap_ι_assoc]
    _ = a' ≫ pV loc x y ≫ (V s t W hinv loc x y).ι ≫ (D loc).ι x := by
        rw [← morphismRestrict_ι_assoc]
    _ = a' ≫ pV loc x y ≫ (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ (D loc).ι y := by
        have := (core loc).t_ι_ι x y
        simp only [core_t, core_V] at this
        rw [show (V s t W hinv loc x y).ι ≫ (D loc).ι x =
          (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ (D loc).ι y from this.symm]
    _ = b' ≫ pV loc y x ≫ (V s t W hinv loc y x).ι ≫ (D loc).ι y := by
        rw [pV_φ_hom_assoc, ← Category.assoc, hab']
    _ = b ≫ chart loc y := by
        rw [morphismRestrict_ι_assoc, liftOverlap_ι_assoc]

noncomputable def pglued : X ⟶ (D loc).glued :=
  (coverW hxW).glueMorphisms (fun x => chart loc x) fun x y =>
    chart_comp_eq loc x y _ _ pullback.condition

lemma ι_pglued (x : X) : (W x).ι ≫ pglued hxW loc = chart loc x :=
  (coverW hxW).ι_glueMorphisms _ _ x

lemma s_pglued : s ≫ pglued hxW loc = t ≫ pglued hxW loc := by
  let 𝒰 : R.OpenCover := Scheme.Cover.mkOfCovers X (fun x => (s ⁻¹ᵁ W x : Scheme.{u}))
    (fun x => (s ⁻¹ᵁ W x).ι) (fun r => ⟨s r, ⟨r, hxW (s r)⟩, rfl⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun x => ?_
  change (s ⁻¹ᵁ W x).ι ≫ s ≫ pglued hxW loc = (s ⁻¹ᵁ W x).ι ≫ t ≫ pglued hxW loc
  rw [← morphismRestrict_ι_assoc, ι_pglued, ← tW_ι_assoc s t W hinv, ι_pglued, chart,
    ← Category.assoc, hw loc x]
  simp only [tW, Category.assoc]

lemma preimage_chart (x : X) :
    pglued hxW loc ⁻¹ᵁ ((D loc).ι x).opensRange = (W x).ι.opensRange := by
  ext z
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · intro hz
    change pglued hxW loc z ∈ Set.range ((D loc).ι x) at hz
    have hzW : z ∈ W z := hxW z
    have hpz : pglued hxW loc z = (D loc).ι z (ploc s t W hinv loc z ⟨z, hzW⟩) := by
      have h := congrArg (fun φ : (W z : Scheme.{u}) ⟶ _ => φ ⟨z, hzW⟩) (ι_pglued hxW loc z)
      simp only [Scheme.Hom.comp_apply] at h
      exact h
    rw [hpz] at hz
    have : ploc s t W hinv loc z ⟨z, hzW⟩ ∈ ((D loc).ι z) ⁻¹ᵁ ((D loc).ι x).opensRange := hz
    rw [(core loc).preimage_opensRange] at this
    have : (⟨z, hzW⟩ : (W z : Scheme.{u})) ∈ ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x := this
    rw [preimage_V] at this
    exact this
  · intro hz
    change pglued hxW loc z ∈ Set.range ((D loc).ι x)
    refine ⟨ploc s t W hinv loc x ⟨z, hz⟩, ?_⟩
    have h := congrArg (fun φ : (W x : Scheme.{u}) ⟶ _ => φ ⟨z, hz⟩) (ι_pglued hxW loc x)
    have h__af := h.symm
    simp only [Scheme.Hom.comp_apply] at h__af
    exact h__af

noncomputable def ιY (x : X) : Yloc s t W hinv loc x ⟶ (D loc).glued := (D loc).ι x

lemma ιY_def (x : X) : ιY loc x = (D loc).ι x := rfl

scoped instance isOpenImmersion_ιY (x : X) : IsOpenImmersion (ιY loc x) :=
  Scheme.GlueData.ι_isOpenImmersion (D loc) (show (core loc).J from x)

lemma isPullback_chart (x : X) :
    IsPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc) :=
  IsOpenImmersion.isPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc)
    (ι_pglued hxW loc x) (preimage_chart hxW loc x)

lemma flat_pglued : Flat (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change Flat (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma lfp_pglued : LocallyOfFinitePresentation (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFinitePresentation) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change LocallyOfFinitePresentation (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma surjective_pglued : Surjective (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change Surjective (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma isPullback_pglued : IsPullback s t (pglued hxW loc) (pglued hxW loc) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (coverW hxW) fun x => ?_
  dsimp only [Scheme.Cover.pullbackHom, Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f, coverW_f, coverW,
    Scheme.Cover.mkOfCovers_X, Scheme.Cover.mkOfCovers_f]
  have K : IsPullback (s ∣_ W x) (tW s t W hinv x ≫ (W x).ι) ((W x).ι ≫ pglued hxW loc)
      (pglued hxW loc) := by
    rw [ι_pglued]
    exact (hpb loc x).paste_vert (isPullback_chart hxW loc x)
  have hsq := (isPullback_morphismRestrict s (W x)).flip
  refine IsPullback.of_iso K hsq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · erw [Iso.refl_hom, Category.comp_id]
    exact hsq.isoPullback_hom_snd.symm
  · erw [Iso.refl_hom, Category.comp_id, tW_ι, ← Category.assoc, hsq.isoPullback_hom_fst]
  · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]; try erw [Category.id_comp]
  · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]; try erw [Category.id_comp]

include hxW loc in
theorem main :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have := flat_pglued hxW loc
  have := lfp_pglued hxW loc
  have := surjective_pglued hxW loc
  have hk : IsKernelPair (pglued hxW loc) s t := isPullback_pglued hxW loc
  exact ⟨_, pglued hxW loc, s_pglued hxW loc, inferInstance, inferInstance, inferInstance,
    isPullback_pglued hxW loc, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi _)⟩⟩

end Main56

/-- Gluing of fppf quotients (the Anthropic FLT result
`AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict` without
finiteness). Let `s t : R ⟶ X` and let `W x` be an open neighbourhood of each point `x` whose
inverse images under `s` and `t` agree. If the relation restricted to each `W x` has a quotient
`p` that is flat, locally of finite presentation and surjective, with the restricted relation as
its kernel pair, then `s t` has such a quotient on all of `X`, and it is the coequalizer of
`s` and `t`. -/
theorem exists_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  main hxW loc

end Langlands.AlgebraicGeometry.FppfQuotientGluing

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- A scheme quotient of an étale equivalence relation `F`: a scheme `M` and an étale surjective
morphism `q : F.U ⟶ M` such that `(F.t, F.s)` identifies `F.R` with `F.U ×_M F.U`. -/
structure SchemeQuotient (F : EtaleEquivalenceRelation.{u}) where
  /-- The quotient scheme. -/
  M : Scheme.{u}
  /-- The quotient morphism. -/
  q : F.U ⟶ M
  /-- `F.R` is the kernel pair of `q` through `F.t` and `F.s`. -/
  isPullback : IsPullback F.t F.s q q
  /-- The quotient morphism is étale. -/
  [etale : Etale q]
  /-- The quotient morphism is surjective. -/
  [surjective : Surjective q]

attribute [instance] SchemeQuotient.etale SchemeQuotient.surjective

variable (F : EtaleEquivalenceRelation.{u})

/-- An affine quotient of the chart relation on an invariant open `V` is a quotient of the
restriction of `F` to the source preimage of `V`, in the form used by
`FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict`. -/
lemma exists_quotient_restrict_of_hasAffineQuotient (V : F.U.Opens) (hV : F.IsInvariantOpen V)
    (h : (F.chart V.ι).HasAffineQuotient) :
    ∃ (Y : Scheme.{u}) (p : V.toScheme ⟶ Y),
      (F.s ∣_ V) ≫ p = ((F.R.isoOfEq hV).hom ≫ (F.t ∣_ V)) ≫ p ∧
      Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (F.s ∣_ V) ((F.R.isoOfEq hV).hom ≫ (F.t ∣_ V)) p p := by
  obtain ⟨M, q, -, hpb, hflat, hlfp, hsurj⟩ := h
  change IsPullback (Chart.t F V.ι) (Chart.s F V.ι) q q at hpb
  have hchart := (F.isCartesianHom_chart_of_isInvariantOpen V hV).2
  change IsPullback (Chart.map F V.ι) (Chart.s F V.ι) F.s V.ι at hchart
  let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict F.s V).flip hchart
  have he_s : e.hom ≫ Chart.s F V.ι = F.s ∣_ V := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have he_map : e.hom ≫ Chart.map F V.ι = (F.s ⁻¹ᵁ V).ι := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have he_t : e.hom ≫ Chart.t F V.ι = (F.R.isoOfEq hV).hom ≫ (F.t ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, ← Chart.map_t, ← Category.assoc, he_map,
      Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
  have hpb' : IsPullback (F.s ∣_ V) ((F.R.isoOfEq hV).hom ≫ (F.t ∣_ V)) q q :=
    hpb.flip.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [he_s, Iso.refl_hom, Category.comp_id])
      (by rw [he_t, Iso.refl_hom, Category.comp_id])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  exact ⟨M, q, hpb'.w, hflat, hlfp, hsurj, hpb'⟩

/-- An étale equivalence relation whose object scheme is covered by invariant opens with affine
chart quotients has a scheme quotient. -/
theorem nonempty_schemeQuotient_of_invariantOpenCover {K : Type*} (V : K → F.U.Opens)
    (hV : iSup V = ⊤) (hinv : ∀ k, F.IsInvariantOpen (V k))
    (hq : ∀ k, (F.chart (V k).ι).HasAffineQuotient) : Nonempty F.SchemeQuotient := by
  have hcov : ∀ x : F.U, ∃ k, x ∈ V k := by
    intro x
    have hx : x ∈ iSup V := by
      rw [hV]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  choose k hk using hcov
  obtain ⟨M, q, -, hflat, hlfp, hsurj, hpb, -⟩ :=
    FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict F.s F.t
      (fun x => V (k x)) hk (fun x => hinv (k x))
      (fun x => F.exists_quotient_restrict_of_hasAffineQuotient (V (k x)) (hinv (k x)) (hq (k x)))
  have : IsZariskiLocalAtTarget @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
  have : Etale q := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hpb.flip
    ⟨⟨hsurj, hflat⟩, hlfp⟩ F.etale_t
  exact ⟨⟨M, q, hpb.flip⟩⟩

/-- The chosen scheme quotient of an étale equivalence relation with an invariant open cover
whose chart relations have affine quotients. -/
noncomputable def schemeQuotientOfInvariantOpenCover {K : Type*} (V : K → F.U.Opens)
    (hV : iSup V = ⊤) (hinv : ∀ k, F.IsInvariantOpen (V k))
    (hq : ∀ k, (F.chart (V k).ι).HasAffineQuotient) : F.SchemeQuotient :=
  (F.nonempty_schemeQuotient_of_invariantOpenCover V hV hinv hq).some

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
