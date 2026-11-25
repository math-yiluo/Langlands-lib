/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject

/-! # The categorical local image on the small étale site

Source: Stacks Project, Tag 00WL, image subsheaves. The construction with epimorphic
sources is the categorical version for Grothendieck abelian coefficients.
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G)

/-- A map into a sheaf value lifts through `p` on a covering sieve. No compatibility
between the lifts is imposed. Source: Stacks Project, Tag 00WL.
(auxiliary; not a blueprint node). -/
def LocallyLifts (W : X.Etale) {B : A} (x : B ⟶ G.obj.obj (op W)) : Prop :=
  ∃ (R : Sieve W), R ∈ X.smallEtaleTopology W ∧
    ∀ (Z : X.Etale) (f : Z ⟶ W), R f →
      ∃ l : B ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = x ≫ G.obj.map f.op

/-- A subobject belongs to the local image if its inclusion lifts locally after an
epimorphism onto its source. Source: Stacks Project, Tag 00WL, categorical image argument.
(auxiliary; not a blueprint node). -/
def LocalImageMember (W : X.Etale) (S : Subobject (G.obj.obj (op W))) : Prop :=
  ∃ (P : A) (e : P ⟶ (S : A)), Epi e ∧ LocallyLifts p W (e ≫ S.arrow)

/-- The union of local-image subobjects, constructed as a supremum in the complete
subobject lattice. Source: Stacks Project, Tag 00WL, categorical image argument.
(auxiliary; not a blueprint node). -/
noncomputable def localImage (W : X.Etale) : Subobject (G.obj.obj (op W)) :=
  sSup {S | LocalImageMember p W S}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma locallyLifts_precomp {W : X.Etale} {B D : A}
    {x : B ⟶ G.obj.obj (op W)} (hx : LocallyLifts p W x) (a : D ⟶ B) :
    LocallyLifts p W (a ≫ x) := by
  obtain ⟨R, hR, h⟩ := hx
  refine ⟨R, hR, fun Z f hf ↦ ?_⟩
  obtain ⟨l, hl⟩ := h Z f hf
  exact ⟨a ≫ l, by simp [Category.assoc, hl]⟩

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma locallyLifts_restrict {W V : X.Etale} {B : A}
    {x : B ⟶ G.obj.obj (op W)} (hx : LocallyLifts p W x) (f : V ⟶ W) :
    LocallyLifts p V (x ≫ G.obj.map f.op) := by
  obtain ⟨R, hR, h⟩ := hx
  refine ⟨R.pullback f, X.smallEtaleTopology.pullback_stable f hR, fun Z g hg ↦ ?_⟩
  obtain ⟨l, hl⟩ := h Z (g ≫ f) hg
  exact ⟨l, by simpa using hl⟩

lemma localImageMember_image {W : X.Etale} {B : A}
    {x : B ⟶ G.obj.obj (op W)} (hx : LocallyLifts p W x) :
    LocalImageMember p W (imageSubobject x) := by
  refine ⟨B, factorThruImageSubobject x, inferInstance, ?_⟩
  simpa using hx

omit [IsGrothendieckAbelian.{u + 1} A] in
lemma localImageMember_exists {W V : X.Etale} {S : Subobject (G.obj.obj (op W))}
    (hS : LocalImageMember p W S) (f : V ⟶ W) :
    LocalImageMember p V ((Subobject.«exists» (G.obj.map f.op)).obj S) := by
  obtain ⟨P, e, he, hx⟩ := hS
  have := he
  obtain ⟨q, hq, hfac⟩ := Subobject.exists_fac (G.obj.map f.op) S
  have := hq
  refine ⟨P, e ≫ q, inferInstance, ?_⟩
  simpa [Category.assoc, hfac] using locallyLifts_restrict p hx f

lemma localImage_restrict {W V : X.Etale} (f : V ⟶ W) :
    (Subobject.«exists» (G.obj.map f.op)).obj (localImage p W) ≤ localImage p V := by
  apply (Subobject.gc_exists_pullback _ _ _).2
  apply sSup_le
  intro S hS
  apply (Subobject.gc_exists_pullback _ _ _).1
  exact le_sSup (localImageMember_exists p hS f)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma locallyLifts_p (W : X.Etale) : LocallyLifts p W (p.hom.app (op W)) := by
  refine ⟨⊤, X.smallEtaleTopology.top_mem W, fun Z f _ ↦ ?_⟩
  exact ⟨F.obj.map f.op, p.hom.naturality f.op⟩

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma locallyLifts_of_cover {W : X.Etale} {B : A} (x : B ⟶ G.obj.obj (op W))
    {ι : Type*} (U : ι → X.Etale) (f : ∀ i, U i ⟶ W)
    (hf : Sieve.ofArrows U f ∈ X.smallEtaleTopology W)
    (hx : ∀ i, LocallyLifts p (U i) (x ≫ G.obj.map (f i).op)) :
    LocallyLifts p W x := by
  let R : Sieve W :=
    { arrows := fun Z a ↦ ∃ l : B ⟶ F.obj.obj (op Z),
        l ≫ p.hom.app (op Z) = x ≫ G.obj.map a.op
      downward_closed := by
        intro Z V a ha b
        obtain ⟨l, hl⟩ := ha
        refine ⟨l ≫ F.obj.map b.op, ?_⟩
        rw [Category.assoc, p.hom.naturality, ← Category.assoc, hl]
        simp [Category.assoc] }
  refine ⟨R, ?_, fun Z a ha ↦ ha⟩
  apply X.smallEtaleTopology.transitive hf R
  intro Z a ha
  obtain ⟨i, t, rfl⟩ := Sieve.ofArrows.exists ha
  obtain ⟨V, hV, hl⟩ := hx i
  apply X.smallEtaleTopology.superset_covering _ (X.smallEtaleTopology.pullback_stable t hV)
  intro Y b hb
  obtain ⟨l, hl⟩ := hl Y (b ≫ t) hb
  exact ⟨l, by simpa [R, Category.assoc] using hl⟩

lemma localImageMember_sup {W : X.Etale} {S T : Subobject (G.obj.obj (op W))}
    (hS : LocalImageMember p W S) (hT : LocalImageMember p W T) :
    LocalImageMember p W (S ⊔ T) := by
  obtain ⟨P, e, he, R, hR, hl⟩ := hS
  obtain ⟨Q, d, hd, V, hV, hk⟩ := hT
  have := he
  have := hd
  have := Subobject.epi_supDesc S T
  refine ⟨P ⊞ Q, biprod.map e d ≫ Subobject.supDesc S T, inferInstance,
    R ⊓ V, X.smallEtaleTopology.intersection_covering hR hV, fun Z f hf ↦ ?_⟩
  obtain ⟨l, hl⟩ := hl Z f hf.1
  obtain ⟨k, hk⟩ := hk Z f hf.2
  refine ⟨biprod.desc l k, ?_⟩
  apply biprod.hom_ext'
  · simp [Category.assoc, hl]
  · simp [Category.assoc, hk]

/-- The local-image subobjects form a small directed family. Using distinct subobjects
avoids imposing filteredness on a category of covering maps.
Source: Stacks Project, Tag 00WL; AB5 categorical image argument.
(auxiliary; not a blueprint node). -/
abbrev LocalImageIndex (W : X.Etale) :=
  Shrink.{u + 1} {S : Subobject (G.obj.obj (op W)) // LocalImageMember p W S}

/-- The subobject indexed by a member of the small local-image family.
(auxiliary; not a blueprint node). -/
noncomputable def localImageFamily (W : X.Etale) (i : LocalImageIndex p W) :
    Subobject (G.obj.obj (op W)) :=
  ((equivShrink _).symm i).val

lemma localImageFamily_mem (W : X.Etale) (i : LocalImageIndex p W) :
    LocalImageMember p W (localImageFamily p W i) :=
  ((equivShrink _).symm i).property

instance localImageIndex_nonempty (W : X.Etale) : Nonempty (LocalImageIndex p W) :=
  ⟨equivShrink _ ⟨imageSubobject (p.hom.app (op W)),
    localImageMember_image p (locallyLifts_p p W)⟩⟩

lemma localImageFamily_directed (W : X.Etale) :
    Directed (· ≤ ·) (localImageFamily p W) := by
  intro i j
  refine ⟨equivShrink _ ⟨_, localImageMember_sup p
    (localImageFamily_mem p W i) (localImageFamily_mem p W j)⟩, ?_, ?_⟩
  · simp [localImageFamily]
  · simp [localImageFamily]

set_option backward.isDefEq.respectTransparency false in
lemma iSup_localImageFamily (W : X.Etale) :
    (⨆ i, localImageFamily p W i) = localImage p W := by
  classical
  let e := equivShrink {S : Subobject (G.obj.obj (op W)) // LocalImageMember p W S}
  rw [← e.surjective.iSup_comp (localImageFamily p W)]
  simp only [localImageFamily, e, Equiv.symm_apply_apply]
  exact (sSup_eq_iSup' {S : Subobject (G.obj.obj (op W)) |
    LocalImageMember p W S}).symm

/-- Extend the local image from the qcqs basis by testing all restrictions to qcqs objects.
It is an actual construction in the subobject lattice, independent of any existence theorem.
Source: Stacks Project, Tag 00WL, image subsheaf argument and restriction to a basis.
(auxiliary; not a blueprint node). -/
noncomputable def qcqsLocalImage (W : X.Etale) : Subobject (G.obj.obj (op W)) :=
  ⨅ (Z : X.Etale) (_ : CompactSpace Z.left) (_ : QuasiSeparatedSpace Z.left)
    (f : Z ⟶ W), (Subobject.pullback (G.obj.map f.op)).obj (localImage p Z)

lemma qcqsLocalImage_restrict {W V : X.Etale} (f : V ⟶ W) :
    (Subobject.«exists» (G.obj.map f.op)).obj (qcqsLocalImage p W) ≤
      qcqsLocalImage p V := by
  apply (Subobject.gc_exists_pullback _ _ _).2
  simp only [qcqsLocalImage, (Subobject.gc_exists_pullback (G.obj.map f.op)).u_iInf]
  apply le_iInf
  intro Z
  apply le_iInf
  intro hZ
  apply le_iInf
  intro hZ'
  apply le_iInf
  intro g
  rw [← Subobject.pullback_comp, ← G.obj.map_comp, ← op_comp]
  exact iInf_le_of_le Z (iInf_le_of_le hZ (iInf_le_of_le hZ'
    (iInf_le _ (g ≫ f))))

lemma localImage_le_qcqsLocalImage (W : X.Etale) : localImage p W ≤ qcqsLocalImage p W := by
  refine le_iInf fun Z ↦ le_iInf fun _ ↦ le_iInf fun _ ↦ le_iInf fun f ↦ ?_
  exact (Subobject.gc_exists_pullback _ _ _).1 (localImage_restrict p f)

lemma qcqsLocalImage_eq (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    qcqsLocalImage p W = localImage p W := by
  refine le_antisymm ?_ (localImage_le_qcqsLocalImage p W)
  have h : qcqsLocalImage p W ≤
      (Subobject.pullback (G.obj.map (𝟙 W).op)).obj (localImage p W) :=
    iInf_le_of_le W (iInf_le_of_le (inferInstance : CompactSpace W.left)
    (iInf_le_of_le (inferInstance : QuasiSeparatedSpace W.left)
      (iInf_le (fun f : W ⟶ W ↦
        (Subobject.pullback (G.obj.map f.op)).obj (localImage p W)) (𝟙 W))))
  simpa [Subobject.pullback_id] using h

/-- The presheaf extending the local image from the qcqs basis.
(auxiliary; not a blueprint node). -/
noncomputable def qcqsLocalImagePresheaf : X.Etaleᵒᵖ ⥤ A where
  obj W := qcqsLocalImage p W.unop
  map {W V} f := (qcqsLocalImage p V.unop).factorThru
    ((qcqsLocalImage p W.unop).arrow ≫ G.obj.map f)
    ((Subobject.exists_le_iff _ _ _).1 (qcqsLocalImage_restrict p f.unop))
  map_id W := by
    apply (cancel_mono (qcqsLocalImage p W.unop).arrow).1
    simp
  map_comp f g := by
    apply (cancel_mono (qcqsLocalImage p _).arrow).1
    simp [Category.assoc]

/-- The inclusion of the presheaf extending the local image from the qcqs basis.
(auxiliary; not a blueprint node). -/
noncomputable def qcqsLocalImageι : qcqsLocalImagePresheaf p ⟶ G.obj where
  app W := (qcqsLocalImage p W.unop).arrow
  naturality W V f := by simp [qcqsLocalImagePresheaf]

lemma qcqsLocalImage_contains_p (W : X.Etale) :
    (qcqsLocalImage p W).Factors (p.hom.app (op W)) := by
  apply Subobject.factors_of_le _ (localImage_le_qcqsLocalImage p W)
  exact (Subobject.imageSubobject_le_iff _ _).1
    (le_sSup (localImageMember_image p (locallyLifts_p p W)))

/-- The given sheaf morphism factors through its qcqs local-image presheaf.
(auxiliary; not a blueprint node). -/
noncomputable def toQcqsLocalImage : F.obj ⟶ qcqsLocalImagePresheaf p where
  app W := (qcqsLocalImage p W.unop).factorThru (p.hom.app W)
    (qcqsLocalImage_contains_p p W.unop)
  naturality W V f := by
    apply (cancel_mono (qcqsLocalImage p V.unop).arrow).1
    simp [Category.assoc, qcqsLocalImagePresheaf, p.hom.naturality]

lemma toQcqsLocalImage_ι : toQcqsLocalImage p ≫ qcqsLocalImageι p = p.hom := by
  ext W
  simp [toQcqsLocalImage, qcqsLocalImageι]

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
