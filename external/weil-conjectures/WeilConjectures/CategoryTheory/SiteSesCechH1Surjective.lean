/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.SiteCechComplex
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Surjectivity of sections from vanishing Čech H¹

Source: Stacks Project, Cohomology on Sites, Lemma 03F8 (lemma-ses-cech-h1)
(blueprint: lem-weil-pbc-site-ses-cech-h1-surjective).

Covering indices and coefficient groups live in universes containing the site's object
and morphism universes. This includes all presieve-indexed coverings and permits larger
index and coefficient universes through `w` and `r`.
-/

@[expose] public section

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma type_toPlus_surjective {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type (max u v r)) :
    Presheaf.IsLocallySurjective J (J.toPlus P) := by
  classical
  constructor
  intro X x
  obtain ⟨R, x, rfl⟩ := GrothendieckTopology.Plus.exists_rep x
  refine J.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) R.2
  open GrothendieckTopology.Plus in
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
  refine ⟨R.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
  ext ⟨Z, g, hg⟩
  simpa using!
    x.2 { fst.hf := hf, snd.hf := R.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

private lemma type_toPlus_injective {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type (max u v r)) :
    Presheaf.IsLocallyInjective J (J.toPlus P) := by
  classical
  constructor
  intro X x y h
  open GrothendieckTopology.Plus in
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
  obtain ⟨W, h₁, h₂, eq⟩ := h
  exact J.superset_covering
    (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2

private lemma type_toSheafify_surjective {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type (max u v r)) :
    Presheaf.IsLocallySurjective J (J.toSheafify P) := by
  have := type_toPlus_surjective.{u,v,r} J P
  have := type_toPlus_surjective.{u,v,r} J (J.plusObj P)
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

private lemma type_toSheafify_injective {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type (max u v r)) :
    Presheaf.IsLocallyInjective J (J.toSheafify P) := by
  have := type_toPlus_injective.{u,v,r} J P
  have := type_toPlus_injective.{u,v,r} J (J.plusObj P)
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Local lifts exist for epimorphisms of abelian sheaves on a site.
Source: Stacks Project, Lemma 03CN(5); this is the general-site local-surjectivity
part of the proof of the present theorem.
(blueprint: lem-weil-pbc-site-ses-cech-h1-surjective) -/
private theorem site_ses_local_lifts
    (C : Type u) [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v r}))
    (hS : S.ShortExact) (U : C) (s : S.X₃.obj.obj (op U)) :
    ∃ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ J U ∧
      ∀ i, ∃ t : S.X₂.obj.obj (op (V i)),
        S.g.hom.app _ t = S.X₃.obj.map (f i).op s := by
  classical
  have : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{max u v r}) :=
    preservesFilteredColimitsOfSize_shrink.{max u v, r, max u v, r} _
  have : HasSheafify J.toGrothendieck AddCommGrpCat.{max u v r} := inferInstance
  have : HasSheafify J.toGrothendieck (Type (max u v r)) := inferInstance
  have : J.toGrothendieck.PreservesSheafification
      (forget AddCommGrpCat.{max u v r}) := inferInstance
  have hsurj (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v r}) :
      Presheaf.IsLocallySurjective J.toGrothendieck (toSheafify J.toGrothendieck P) := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      ← sheafComposeIso_hom_fac, ← toSheafify_plusPlusIsoSheafify_hom]
    have := type_toSheafify_surjective.{u,v,r} J.toGrothendieck (P ⋙ forget _)
    infer_instance
  have hinj (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v r}) :
      Presheaf.IsLocallyInjective J.toGrothendieck (toSheafify J.toGrothendieck P) := by
    rw [← Presheaf.isLocallyInjective_forget_iff,
      ← sheafComposeIso_hom_fac, ← toSheafify_plusPlusIsoSheafify_hom]
    have := type_toSheafify_injective.{u,v,r} J.toGrothendieck (P ⋙ forget _)
    infer_instance
  have : J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    GrothendieckTopology.WEqualsLocallyBijective.mk' _ _
  have := hS.epi_g
  have : Presheaf.IsLocallySurjective J.toGrothendieck S.g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v r} S.g).2 this
  obtain ⟨R, hR, hle⟩ :=
    (J.mem_toGrothendieck_iff_of_isStableUnderComposition).1
      (Presheaf.imageSieve_mem J.toGrothendieck S.g.hom s)
  let I := ULift.{w} (Σ Y : C, {a : Y ⟶ U // R a})
  let V : I → C := fun i ↦ i.down.1
  let f : ∀ i : I, V i ⟶ U := fun i ↦ i.down.2.1
  have hcov : Presieve.ofArrows V f ∈ J U := by
    have heq : Presieve.ofArrows V f = R := by
      funext Y a
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.down.2.2
      · intro ha
        exact Presieve.ofArrows.mk (⟨⟨Y, a, ha⟩⟩ : I)
    rwa [heq]
  exact ⟨I, V, f, hcov, fun i ↦ hle _ _ i.down.2.2⟩

private lemma site_projection_ext {C : Type u} [Category.{v} C]
    {I : Type w} {U : C} {V : I → C} {f : ∀ i, V i ⟶ U}
    (T : SiteCechComplex V f) {p : ℕ} {z : Fin (p + 1) → I} {Z : C}
    (a b : Z ⟶ T.W p z) (h : ∀ k, a ≫ T.pr p z k = b ≫ T.pr p z k) : a = b := by
  obtain ⟨c, _, hu⟩ := T.universal p z Z (fun k ↦ b ≫ T.pr p z k)
    (fun k ↦ by simp only [Category.assoc, T.comm])
  exact (hu a h).trans (hu b (fun _ ↦ rfl)).symm

private lemma site_cochain_congr {C : Type u} [Category.{v} C]
    {I : Type w} {U : C} {V : I → C} {f : ∀ i, V i ⟶ U}
    (T : SiteCechComplex V f) (P : Cᵒᵖ ⥤ AddCommGrpCat.{r})
    {p : ℕ} (c : T.cochains P p) {z z' : Fin (p + 1) → I} (h : z = z')
    {Z : C} (a : Z ⟶ T.W p z) (b : Z ⟶ T.W p z')
    (hab : a ≫ eqToHom (congrArg (T.W p) h) = b) :
    P.map a.op (c z) = P.map b.op (c z') := by
  subst h hab
  simp

private lemma site_d_zero_restrict {C : Type u} [Category.{v} C]
    {I : Type w} {U : C} {V : I → C} {f : ∀ i, V i ⟶ U}
    (T : SiteCechComplex V f) (P : Cᵒᵖ ⥤ AddCommGrpCat.{r})
    (s : P.obj (op U)) (a : T.cochains P 0)
    (ha : ∀ z, a z = P.map (T.pr 0 z 0 ≫ f (z 0)).op s) :
    (T.complex P).d 0 1 a = 0 := by
  funext z
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
    P.map (T.indexMap z j.succAbove).op (a (z ∘ j.succAbove))) = 0
  have h (j : Fin 2) :
      P.map (T.indexMap z j.succAbove).op (a (z ∘ j.succAbove)) =
        P.map (T.pr 1 z 0 ≫ f (z 0)).op s := by
    rw [ha, ← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
    rw [← Category.assoc, T.indexMap_pr]
    exact congrArg (fun a ↦ P.map a.op s) (T.comm 1 z (j.succAbove 0))
  simp only [h]
  simp [Fin.sum_univ_two]

private lemma site_map_d {C : Type u} [Category.{v} C]
    {I : Type w} {U : C} {V : I → C} {f : ∀ i, V i ⟶ U}
    (T : SiteCechComplex V f) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{r}}
    (φ : P ⟶ Q) (p : ℕ) (a : T.cochains P p) :
    T.cochainsMap φ (p + 1) ((T.complex P).d p (p + 1) a) =
      (T.complex Q).d p (p + 1) (T.cochainsMap φ p a) :=
  (ConcreteCategory.congr_hom (T.cochainsMap_comm φ p) a).symm

private lemma site_compatible {C : Type u} [Category.{v} C]
    {I : Type w} {U : C} {V : I → C} {f : ∀ i, V i ⟶ U}
    (T : SiteCechComplex V f) (P : Cᵒᵖ ⥤ AddCommGrpCat.{r})
    (c : T.cochains P 0) (hc : (T.complex P).d 0 1 c = 0)
    (z z' : Fin 1 → I) {Z : C} (a : Z ⟶ T.W 0 z) (b : Z ⟶ T.W 0 z')
    (hab : a ≫ T.pr 0 z 0 ≫ f (z 0) = b ≫ T.pr 0 z' 0 ≫ f (z' 0)) :
    P.map a.op (c z) = P.map b.op (c z') := by
  let y : Fin 2 → I := Fin.cons (z 0) z'
  let q : ∀ k : Fin 2, Z ⟶ V (y k) :=
    Fin.cases (a ≫ T.pr 0 z 0) (fun k ↦ b ≫ T.pr 0 z' k)
  have hq : ∀ k, q k ≫ f (y k) = q 0 ≫ f (y 0) := by
    intro k
    fin_cases k
    · rfl
    · change (b ≫ T.pr 0 z' 0) ≫ f (z' 0) =
        (a ≫ T.pr 0 z 0) ≫ f (z 0)
      simpa only [Category.assoc] using hab.symm
  obtain ⟨G, hG, _⟩ := T.universal 1 y Z q hq
  have h := congrArg (fun x ↦ P.map G.op (x y)) hc
  change P.map G.op (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
    P.map (T.indexMap y j.succAbove).op (c (y ∘ j.succAbove))) = P.map G.op 0 at h
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_smul, neg_smul, map_neg, map_add, map_zero] at h
  rw [add_neg_eq_zero] at h
  have h₀ : y ∘ (0 : Fin 2).succAbove = z' := by
    funext k
    fin_cases k
    rfl
  have h₁ : y ∘ (1 : Fin 2).succAbove = z := by
    funext k
    fin_cases k
    rfl
  have face {z'' : Fin 1 → I} (j : Fin 2) (hj : y ∘ j.succAbove = z'')
      (d : Z ⟶ T.W 0 z'')
      (hd : ∀ k, d ≫ T.pr 0 z'' k =
        q (j.succAbove k) ≫ eqToHom (congrArg V (congrFun hj k))) :
      P.map G.op (P.map (T.indexMap y j.succAbove).op (c (y ∘ j.succAbove))) =
        P.map d.op (c z'') := by
    rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
    apply site_cochain_congr T P c hj
    apply site_projection_ext T
    intro k
    subst z''
    simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    rw [T.indexMap_pr, hG]
    simpa only [eqToHom_refl, Category.comp_id] using (hd k).symm
  have hfa := face 1 h₁ a (fun k ↦ by fin_cases k; simp only [eqToHom_refl, Category.comp_id]; rfl)
  have hfb := face 0 h₀ b (fun k ↦ by fin_cases k; simp only [eqToHom_refl, Category.comp_id]; rfl)
  exact hfa.symm.trans (h.symm.trans hfb)

set_option linter.unusedVariables false in
/-- A short exact sequence of abelian sheaves on a site is surjective on sections over `U`
if the kernel has vanishing Čech H¹ on a cofinal system of coverings.
Source: Stacks Project, Cohomology on Sites, Lemma 03F8
(blueprint: lem-weil-pbc-site-ses-cech-h1-surjective).

Proof:
1. Short exactness gives a sectionwise injective kernel map, with image the kernel of
   the second map, using situation-conventions and
   def-weil-pbc-exact-sequence.
2. Given a section of the quotient, the epimorphism has local lifts on a covering by
   lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective.
3. Refine this covering into the cofinal system and restrict its lifts; naturality
   preserves their images and the selected covering has vanishing Čech H¹.
4. On each double overlap take the second lift minus the first. Sectionwise exactness
   gives a unique kernel-valued cochain. On triple overlaps its alternating differential
   is zero, because the three differences cancel and the kernel map is injective.
5. By def-weil-pbc-site-cech-complex, vanishing H¹ makes this cocycle the differential
   of a 0-cochain. Subtract its image from the local lifts: they now agree on overlaps,
   and their images still equal the restrictions of the original quotient section.
6. The sheaf condition of the middle sheaf glues these corrected lifts. Separatedness
   of the quotient sheaf shows the glued section maps to the original section. -/
theorem surjective_sections_of_site_cech_h1_vanishing
    (C : Type u) [Category.{v} C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v r}))
    (hS : S.ShortExact) (U : C)
    (Cov : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U), Prop)
    (hcover : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Cov I V f → Presieve.ofArrows V f ∈ J U)
    (hcofinal : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Presieve.ofArrows V f ∈ J U →
      ∃ (K : Type (max u v w)) (W : K → C) (g : ∀ k, W k ⟶ U),
        Cov K W g ∧ ∀ k, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k)
    (hcech : ∀ (I : Type (max u v w)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Cov I V f → ∀ (T : SiteCechComplex V f),
        IsZero ((T.cohomologyFunctor 1).obj S.X₁.1)) :
    Function.Surjective (S.g.hom.app (op U)) := by
  classical
  have : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{max u v r}) :=
    preservesFilteredColimitsOfSize_shrink.{max u v, r, max u v, r} _
  have : HasSheafify J.toGrothendieck AddCommGrpCat.{max u v r} := inferInstance
  intro s
  obtain ⟨I, V, f, hcov, hlift⟩ := site_ses_local_lifts.{u,v,w,r} C J S hS U s
  obtain ⟨K, W, g, hCov, href⟩ := hcofinal I V f hcov
  have hlift' : ∀ k, ∃ t : S.X₂.obj.obj (op (W k)),
      S.g.hom.app _ t = S.X₃.obj.map (g k).op s := by
    intro k
    obtain ⟨i, a, ha⟩ := href k
    obtain ⟨t, ht⟩ := hlift i
    refine ⟨S.X₂.obj.map a.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, ha]
  choose t ht using hlift'
  obtain ⟨T⟩ := SiteCechComplex.exists_of_covering J (hcover K W g hCov)
  let a : T.cochains S.X₂.obj 0 := fun z ↦
    S.X₂.obj.map (T.pr 0 z 0).op (t (z 0))
  have ha (z) : T.cochainsMap S.g.hom 0 a z =
      S.X₃.obj.map (T.pr 0 z 0 ≫ g (z 0)).op s := by
    change S.g.hom.app _ (S.X₂.obj.map _ _) = _
    rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp]
  have hex (Y : Cᵒᵖ) (x : S.X₂.obj.obj Y) (hx : S.g.hom.app Y x = 0) :
      ∃ y, S.f.hom.app Y y = x := by
    have := hS.mono_f
    exact (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
      (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj Y) inferInstance inferInstance) x hx
  have hinj (Y : Cᵒᵖ) : Function.Injective (S.f.hom.app Y) := by
    have := hS.mono_f
    exact (AddCommGrpCat.mono_iff_injective _).1
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj Y).map_mono S.f)
  have hzero : T.cochainsMap S.g.hom 1 ((T.complex S.X₂.obj).d 0 1 a) = 0 := by
    rw [site_map_d]
    exact site_d_zero_restrict T _ s _ ha
  choose e he using fun z ↦ hex (op (T.W 1 z))
    (((T.complex S.X₂.obj).d 0 1 a) z) (congrFun hzero z)
  have he' : T.cochainsMap S.f.hom 1 e = (T.complex S.X₂.obj).d 0 1 a := funext he
  have hec : (T.complex S.X₁.obj).d 1 2 e = 0 := by
    have h : T.cochainsMap S.f.hom 2 ((T.complex S.X₁.obj).d 1 2 e) = 0 := by
      rw [site_map_d, he']
      exact ConcreteCategory.congr_hom ((T.complex S.X₂.obj).d_comp_d 0 1 2) a
    funext z
    apply hinj _
    change S.f.hom.app _ (((T.complex S.X₁.obj).d 1 2 e) z) = S.f.hom.app _ 0
    rw [map_zero]
    exact congrFun h z
  have hA : (T.complex S.X₁.obj).ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ 1).2 (hcech K W g hCov T)
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hA
  obtain ⟨b, hb⟩ := hA e hec
  change (T.complex S.X₁.obj).d 0 1 b = e at hb
  let c : T.cochains S.X₂.obj 0 := a - T.cochainsMap S.f.hom 0 b
  have hc : (T.complex S.X₂.obj).d 0 1 c = 0 := by
    change (T.complex S.X₂.obj).d 0 1 (a - T.cochainsMap S.f.hom 0 b) = 0
    rw [map_sub, ← site_map_d, hb, he', sub_self]
  have hgcf (Y : Cᵒᵖ) (x : S.X₁.obj.obj Y) : S.g.hom.app Y (S.f.hom.app Y x) = 0 :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun φ ↦ φ.hom) S.zero) Y) x
  have hcov' : Sieve.ofArrows (fun z : Fin 1 → K ↦ T.W 0 z)
      (fun z ↦ T.pr 0 z 0 ≫ g (z 0)) ∈ J.toGrothendieck U := by
    apply J.toGrothendieck.superset_covering _
      (J.generate_mem_toGrothendieck (hcover K W g hCov))
    intro Y f hf
    obtain ⟨i, d, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    refine (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨fun _ ↦ i, d ≫ eqToHom (T.W_zero (fun _ ↦ i)).symm, ?_⟩
    rw [T.pr_zero]
    simp
  have hsh (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v r}) :
      Presieve.IsSheafFor (F.obj ⋙ forget _) (Presieve.ofArrows
        (fun z : Fin 1 → K ↦ T.W 0 z) (fun z ↦ T.pr 0 z 0 ≫ g (z 0))) := by
    have h := (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget AddCommGrpCat) F.property)
    rw [Presieve.isSheafFor_iff_generate]
    exact h _ hcov'
  obtain ⟨σ, hσ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 (hsh S.X₂) c
    (fun z z' Z d₁ d₂ hd ↦ site_compatible T _ c hc z z' d₁ d₂ hd)
  refine ⟨σ, (hsh S.X₃).isSeparatedFor.ext fun Y f ⟨z⟩ ↦ ?_⟩
  change S.X₃.obj.map _ (S.g.hom.app _ σ) = S.X₃.obj.map _ s
  rw [← NatTrans.naturality_apply]
  erw [hσ z]
  change S.g.hom.app _ (a z - S.f.hom.app _ (b z)) = _
  rw [map_sub, hgcf, sub_zero]
  exact ha z

end CategoryTheory
