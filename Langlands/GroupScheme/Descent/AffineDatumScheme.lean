import Langlands.GroupScheme.Descent.DatumRelation
import Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # The underlying affine scheme of a Čech datum -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}

/-- An affine solution for the underlying scheme, with its actual quotient map. -/
structure AffineSchemeSolution (D : Datum p G) where
  obj : Over B
  affine : IsAffine obj.left
  proj : G.X.left ⟶ obj.left
  square : IsPullback G.X.hom proj p obj.hom
  relation : D.source ≫ proj = D.target ≫ proj

attribute [instance] AffineSchemeSolution.affine

namespace AffineSchemeSolution

variable {D : Datum p G} (s : AffineSchemeSolution D)

/-- The actual slice pullback identifies with the supplied underlying scheme. -/
def iso : (Over.pullback p).obj s.obj ≅ G.X :=
  Over.isoMk s.square.flip.isoPullback.symm (by simp)

@[reassoc (attr := simp)] theorem iso_hom_proj :
    s.iso.hom.left ≫ s.proj = pullback.fst s.obj.hom p := by
  exact s.square.flip.isoPullback_inv_fst

@[reassoc (attr := simp)] theorem iso_inv_fst :
    s.iso.inv.left ≫ pullback.fst s.obj.hom p = s.proj := by
  exact s.square.flip.isoPullback_hom_fst

/-- The original relation is the entire scheme-theoretic kernel pair of the quotient. -/
theorem kernelPair : IsPullback D.source D.target s.proj s.proj := by
  have hout : IsPullback (D.source ≫ G.X.hom) D.target p (s.proj ≫ s.obj.hom) := by
    have h := D.target_pullback.flip.paste_horiz (IsPullback.of_hasPullback p p)
    rw [← D.source_base, s.square.w] at h
    exact h
  exact hout.of_right s.relation s.square

instance instAffineDatumScheme1 [Flat p] : Flat s.proj :=
  MorphismProperty.of_isPullback (P := @Flat) s.square inferInstance

instance instAffineDatumScheme2 [Surjective p] : Surjective s.proj :=
  MorphismProperty.of_isPullback (P := @Surjective) s.square inferInstance

instance instAffineDatumScheme3 [QuasiCompact p] : QuasiCompact s.proj :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) s.square inferInstance

/-- The kernel pair turns relation invariance into equality above equal quotient images. -/
theorem comp_eq_of_proj_eq {T Z : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) (a b : Z ⟶ G.X.left)
    (hab : a ≫ s.proj = b ≫ s.proj) : a ≫ f = b ≫ f := by
  let r := s.kernelPair.lift a b hab
  calc
    a ≫ f = r ≫ D.source ≫ f := by simp [r]
    _ = r ≫ D.target ≫ f := by rw [hf]
    _ = b ≫ f := by simp [r]

variable [Flat p] [Surjective p] [QuasiCompact p]

/-- Any map constant on the datum's relation factors through the actual quotient. -/
def desc {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) : s.obj.left ⟶ T :=
  EffectiveEpi.desc s.proj f (fun a b hab => s.comp_eq_of_proj_eq f hf a b hab)

@[reassoc] theorem desc_fac {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) : s.proj ≫ s.desc f hf = f := by
  exact EffectiveEpi.fac s.proj f (fun a b hab => s.comp_eq_of_proj_eq f hf a b hab)

theorem desc_unique {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) (a : s.obj.left ⟶ T)
    (ha : s.proj ≫ a = f) : a = s.desc f hf := by
  apply (cancel_epi s.proj).mp
  rw [ha, s.desc_fac]

end AffineSchemeSolution

namespace Datum

open Langlands.AlgebraicGeometry FaithfullyFlatCoalgebraDescent

variable (D : Datum p G) [IsAffine B] [IsAffine S] [IsAffine G.X.left]
    [Flat p] [Surjective p]

/-- Effective affine ring descent constructs the underlying affine solution. -/
theorem nonempty_affineSchemeSolution : Nonempty (AffineSchemeSolution D) := by
  have hO : IsAffine (Overlap p) := IsAffine.of_isPullback (IsPullback.of_hasPullback p p)
  have hR : IsAffine D.relationScheme := IsAffine.of_isPullback D.source_pullback
  obtain ⟨diag, hdt, hds⟩ := D.relation_refl G.X.left (𝟙 _)
  obtain ⟨comp, hct, hcs⟩ := D.relation_trans _
    (pullback.fst D.target D.source) (pullback.snd D.target D.source) pullback.condition
  have hout : IsPullback (D.source ≫ G.X.hom) D.target p (G.X.hom ≫ p) := by
    have h := D.target_pullback.flip.paste_horiz (IsPullback.of_hasPullback p p)
    rwa [← D.source_base] at h
  have hP := isPushout_appTop_of_isPullback hout
  have hP₂ := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback D.target D.source)
  have hφ : p.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p).mp ⟨inferInstance, inferInstance⟩
  have hw : D.source ≫ G.X.hom ≫ p = D.target ≫ G.X.hom ≫ p := D.relation_base
  have hmem : ∀ a, G.X.hom.appTop.hom (p.appTop.hom a) ∈
      D.source.appTop.hom.eqLocus D.target.appTop.hom := fun a =>
    congrArg (fun k : D.relationScheme ⟶ B => k.appTop.hom a) hw
  have key := isPushout_eqLocus_of_groupoid p.appTop.hom hφ G.X.hom.appTop.hom
    D.source.appTop.hom D.target.appTop.hom diag.appTop.hom
    (pullback.fst D.target D.source).appTop.hom
    (pullback.snd D.target D.source).appTop.hom comp.appTop.hom hP hP₂
    (congrArg (fun k => k.appTop.hom) hdt) (congrArg (fun k => k.appTop.hom) hds)
    (congrArg (fun k => k.appTop.hom) hct) (congrArg (fun k => k.appTop.hom) hcs) hmem
  let A : Subring Γ(G.X.left, ⊤) := D.source.appTop.hom.eqLocus D.target.appTop.hom
  let iA : Γ(B, ⊤) →+* A := (G.X.hom.appTop.hom.comp p.appTop.hom).codRestrict _ hmem
  let C : Scheme.{u} := Spec (CommRingCat.of A)
  let c : C ⟶ B := Spec.map (CommRingCat.ofHom iA) ≫ B.isoSpec.inv
  let q : G.X.left ⟶ C := G.X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom A.subtype)
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ key
  have hpb : IsPullback G.X.hom q p c := by
    refine hsq.of_iso G.X.left.isoSpec.symm S.isoSpec.symm (Iso.refl _) B.isoSpec.symm
      ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, CommRingCat.ofHom_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, q, Iso.inv_hom_id_assoc]
      rfl
    · simp only [Iso.symm_hom, CommRingCat.ofHom_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, c]
      rfl
  have hq : D.source ≫ q = D.target ≫ q := by
    simp only [q, ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact a.2
  exact ⟨⟨Over.mk c, (by change IsAffine (Spec (CommRingCat.of A)); infer_instance),
    q, hpb, hq⟩⟩

/-- Choose the constructed underlying affine solution. -/
def affineSchemeSolution : AffineSchemeSolution D :=
  Classical.choice D.nonempty_affineSchemeSolution

end Datum
end Langlands.GroupScheme.Descent
