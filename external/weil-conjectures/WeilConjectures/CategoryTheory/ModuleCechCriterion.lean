/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteCechComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Injectives and the module Čech acyclicity criterion

Source: Stacks Project, Cohomology on Sites, Tags 03F9, 03FB, 03FC;
blueprint, Proper base change, Injectives and the Cech acyclicity criterion
(blueprint: lemma-acyclicity-pulled-back-injectives).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private def reindexCech {C : Type u} [SmallCategory C] {T : Type*} {U : C}
    {V : T → C} {f : ∀ t, V t ⟶ U} (S : SiteCechComplex V f)
    {T' : Type*} (a : T' → T) : SiteCechComplex (V ∘ a) (fun t ↦ f (a t)) where
  W p t := S.W p (a ∘ t)
  pr p t k := S.pr p (a ∘ t) k
  comm p t k := S.comm p (a ∘ t) k
  universal p t Z b hb := S.universal p (a ∘ t) Z b hb
  W_zero t := S.W_zero (a ∘ t)
  pr_zero t := S.pr_zero (a ∘ t)
  indexMap t α := S.indexMap (a ∘ t) α
  indexMap_pr t α k := S.indexMap_pr (a ∘ t) α k

private theorem unliftExact {C : Type u} [SmallCategory C] {T : Type*} {U : C}
    {V : T → C} {f : ∀ t, V t ⟶ U} (S : SiteCechComplex V f)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ)
    (h : ((reindexCech S (ULift.down : ULift.{u} T → T)).complex F).ExactAt
      (q + 1)) : (S.complex F).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h ⊢
  intro c hc
  change (S.complex F).d (q + 1) ((q + 1) + 1) c = 0 at hc
  simp only [SiteCechComplex.complex, CochainComplex.of_d] at hc
  let c' : (reindexCech S (ULift.down : ULift.{u} T → T)).cochains F (q + 1) :=
    fun t ↦ c (ULift.down ∘ t)
  have hc' : ((reindexCech S (ULift.down : ULift.{u} T → T)).complex F).d
      (q + 1) (q + 2) c' = 0 := by
    change (CochainComplex.of.d ((reindexCech S (ULift.down : ULift.{u} T → T)).cochains F)
      ((reindexCech S (ULift.down : ULift.{u} T → T)).differential F) (q + 1) ((q + 1) + 1)) c' = 0
    rw [CochainComplex.of_d]
    funext t
    have hh := congrFun hc (ULift.down ∘ t)
    change S.differentialValue F (q + 1) c _ = 0 at hh
    change (reindexCech S _).differentialValue F (q + 1) c' t = 0
    exact hh
  obtain ⟨d, hd⟩ := h c' hc'
  change (CochainComplex.of.d ((reindexCech S (ULift.down : ULift.{u} T → T)).cochains F)
      ((reindexCech S (ULift.down : ULift.{u} T → T)).differential F) q (q + 1)) d = c' at hd
  rw [CochainComplex.of_d] at hd
  refine ⟨fun t ↦ d (ULift.up ∘ t), ?_⟩
  change (CochainComplex.of.d (S.cochains F) (S.differential F) q (q + 1))
    (fun t ↦ d (ULift.up ∘ t)) = c
  rw [CochainComplex.of_d]
  funext t
  have hh := congrFun hd (ULift.up ∘ t)
  change (reindexCech S _).differentialValue F q d _ = _ at hh
  change S.differentialValue F q (fun t ↦ d (ULift.up ∘ t)) t = c t
  exact hh

private theorem liftExact {C : Type u} [SmallCategory C] {T : Type*} {U : C}
    {V : ULift.{u} T → C} {f : ∀ t, V t ⟶ U} (S : SiteCechComplex V f)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℕ)
    (h : ((reindexCech S ULift.up).complex F).ExactAt (q + 1)) :
    (S.complex F).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h ⊢
  intro c hc
  change (S.complex F).d (q + 1) ((q + 1) + 1) c = 0 at hc
  simp only [SiteCechComplex.complex, CochainComplex.of_d] at hc
  let c' : (reindexCech S ULift.up).cochains F (q + 1) := fun t ↦ c (ULift.up ∘ t)
  have hc' : ((reindexCech S ULift.up).complex F).d (q + 1) (q + 2) c' = 0 := by
    change (CochainComplex.of.d ((reindexCech S ULift.up).cochains F)
      ((reindexCech S ULift.up).differential F) (q + 1) ((q + 1) + 1)) c' = 0
    rw [CochainComplex.of_d]
    funext t
    have hh := congrFun hc (ULift.up ∘ t)
    change S.differentialValue F (q + 1) c _ = 0 at hh
    change (reindexCech S _).differentialValue F (q + 1) c' t = 0
    exact hh
  obtain ⟨d, hd⟩ := h c' hc'
  change (CochainComplex.of.d ((reindexCech S ULift.up).cochains F)
      ((reindexCech S ULift.up).differential F) q (q + 1)) d = c' at hd
  rw [CochainComplex.of_d] at hd
  refine ⟨fun t ↦ d (ULift.down ∘ t), ?_⟩
  change (CochainComplex.of.d (S.cochains F) (S.differential F) q (q + 1))
    (fun t ↦ d (ULift.down ∘ t)) = c
  rw [CochainComplex.of_d]
  funext t
  have hh := congrFun hd (ULift.down ∘ t)
  change (reindexCech S _).differentialValue F q d _ = _ at hh
  change S.differentialValue F q (fun t ↦ d (ULift.down ∘ t)) t = c t
  exact hh

set_option linter.unusedVariables false in
/-- Injective module sheaves are Čech-acyclic; finite-basis Čech-acyclic module sheaves
have zero positive derived sections. The last clause computes derived sections on every
injective resolution in module sheaves, rather than resolving the underlying abelian sheaf.
`products` chooses the iterated products, and `hproducts` expresses closure of the basis
for these choices. Ordered tuples, including repetitions, are built into `SiteCechComplex`.
Source: Stacks Project, Cohomology on Sites, Tags 03F9, 03FB, 03FC
(blueprint: lemma-acyclicity-pulled-back-injectives).

Proof:
1. The finite basis coverings are cofinal by `hrefine`; their chosen iterated products
   lie in the basis by `hproducts` (def-weil-pbc-site-cech-complex). No coproduct in C is used.
2. An injective module sheaf is an injective module presheaf by
   lem-weil-pbc-ringed-site-injective-module-injective-presheaf. The cocycle lifting of
   lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift makes every positive cocycle
   a boundary. The shared universe contains the required free module presheaves.
3. Module sheaves form a Grothendieck abelian category by
   lem-weil-pbc-ring-sheaves-grothendieck, hence have enough injectives by
   lem-sp-grothendieck-enough-injectives. Embed a Čech-acyclic A into an injective I and
   take Q = I/A. The underlying abelian sheaves form a short exact sequence: kernels
   are sectionwise (situation-conventions), and module sheafification has
   underlying abelian sheafification (def-weil-presheaf-modules-sheafification).
4. For U in B, lem-weil-pbc-site-ses-cech-h1-surjective gives I(U) → Q(U) surjective.
   Indeed lift a section locally on a finite basis refinement. The differences form an
   A-valued one-cocycle on overlaps. Its primitive adjusts the lifts to agree, so they
   glue. Left exactness then gives a short exact section sequence on each basis object.
5. Finite products of these sequences over all ordered tuples are short exact in each
   degree. Naturality commutes with alternating restrictions. The long exact sequence
   of lem-weil-pbc-complex-ses-homology-long-exact shows positive Čech cohomology of Q
   vanishes, between the zero groups for I and A.
6. Evaluation is additive and left exact. Apply lem-weil-pbc-derived-functor-long-exact
   and lem-weil-pbc-derived-functor-injective-vanishing in module sheaves. Surjectivity
   in step 4 gives H¹(U,A)=0. For q>1 dimension shifting identifies H^q(U,A) with
   H^(q-1)(U,Q). Induct on q for all Čech-acyclic A, using step 5 for Q. Finally use
   InjectiveResolution.isoRightDerivedObj (def-sp-left-exact-additive) to compute on
   any chosen module injective resolution of M. -/
theorem module_cech_acyclicity_criterion
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck RingCat.{u})
    (B : Set C)
    (hbasis : ∀ U : C, ∃ (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈ J U ∧ ∀ t, V t ∈ B)
    (products : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      U ∈ B → (∀ t, V t ∈ B) → Presieve.ofArrows V f ∈ J U → SiteCechComplex V f)
    (hproducts : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (hU : U ∈ B) (hV : ∀ t, V t ∈ B) (hc : Presieve.ofArrows V f ∈ J U)
      (p : ℕ) (a : Fin (p + 1) → T), (products U T V f hU hV hc).W p a ∈ B)
    (hrefine : ∀ (U : C), U ∈ B →
      ∀ (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Presieve.ofArrows V f ∈ J U →
      ∃ (m : ℕ) (W : Fin m → C) (g : ∀ a, W a ⟶ U),
        (∀ a, W a ∈ B) ∧ Presieve.ofArrows W g ∈ J U ∧
          ∀ a, ∃ (t : T) (k : W a ⟶ V t), k ≫ f t = g a) :
    (∀ (I : ringedSiteModules.{u} R), Injective I →
      ∀ (U : C) (m : ℕ) (V : Fin m → C) (f : ∀ a, V a ⟶ U),
        U ∈ B → (∀ a, V a ∈ B) → Presieve.ofArrows V f ∈ J U →
        ∀ (S : SiteCechComplex V f) (p : ℕ), 0 < p →
          IsZero ((S.cohomologyFunctor p).obj I.val.presheaf)) ∧
    (∀ (M : ringedSiteModules.{u} R),
      (∀ (U : C) (m : ℕ) (V : Fin m → C) (f : ∀ a, V a ⟶ U),
        U ∈ B → (∀ a, V a ∈ B) → Presieve.ofArrows V f ∈ J U →
        ∀ (S : SiteCechComplex V f) (p : ℕ), 0 < p →
          IsZero ((S.cohomologyFunctor p).obj M.val.presheaf)) →
      ∀ (U : C), U ∈ B → ∀ (q : ℕ), 0 < q →
        ∀ (I : InjectiveResolution M),
          IsZero ((((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex).homology q)) := by
  classical
  have hinj (I : ringedSiteModules.{u} R) [Injective I]
      {T : Type u} {U : C} (V : T → C) (f : ∀ a, V a ⟶ U)
      (S : SiteCechComplex V f) (p : ℕ) (hp : 0 < p) :
      IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
    have : Injective I.val := injective_module_sheaf_injective_presheaf R I
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    change IsZero ((S.complex I.val.presheaf).homology (q + 1))
    apply HomologicalComplex.ExactAt.isZero_homology
    apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
      q (q + 1) (q + 2) (by simp) (by simp)).2
    rw [ShortComplex.ab_exact_iff]
    intro c hc
    change (CochainComplex.of.d (S.cochains I.val.presheaf)
      (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
    rw [CochainComplex.of_d] at hc
    obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift
      R.obj I.val V f S q c hc
    refine ⟨b, ?_⟩
    change (CochainComplex.of.d (S.cochains I.val.presheaf)
      (S.differential I.val.presheaf) q (q + 1)) b = c
    rw [CochainComplex.of_d]
    exact hb
  constructor
  · intro I hI U m V f hU hV hc S p hp
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    apply HomologicalComplex.ExactAt.isZero_homology
    apply unliftExact S I.val.presheaf q
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hinj I (V ∘ ULift.down) (fun a ↦ f a.down)
        (reindexCech S ULift.down) (q + 1) (Nat.zero_lt_succ q))
  · let P (M : ringedSiteModules.{u} R) : Prop :=
      ∀ (U : C) (m : ℕ) (V : Fin m → C) (f : ∀ a, V a ⟶ U),
        U ∈ B → (∀ a, V a ∈ B) → Presieve.ofArrows V f ∈ J U →
        ∀ (S : SiteCechComplex V f) (p : ℕ), 0 < p →
          IsZero ((S.cohomologyFunctor p).obj M.val.presheaf)
    let T := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj
    have hsurj (A : ShortComplex (ringedSiteModules.{u} R)) (hA : A.ShortExact)
        (h₁ : P A.X₁) (U : C) (hU : U ∈ B) :
        Function.Surjective ((T.map A.g).app (op U)) := by
      let E := A.map (SheafOfModules.toSheaf R)
      have hE : E.ShortExact := hA.map_of_exact _
      let Cov := fun (K : Type u) (V : K → C) (f : ∀ a, V a ⟶ U) ↦
        (∃ m : ℕ, K = ULift.{u} (Fin m)) ∧
          (∀ a, V a ∈ B) ∧ Presieve.ofArrows V f ∈ J U
      apply surjective_sections_of_site_cech_h1_vanishing C J E hE U Cov
      · intro K V f hc
        exact hc.2.2
      · intro K V f hc
        obtain ⟨m, W, g, hW, hcov, href⟩ := hrefine U hU K V f hc
        refine ⟨ULift.{u} (Fin m), W ∘ ULift.down, (fun a ↦ g a.down),
          ⟨⟨m, rfl⟩, (fun a ↦ hW a.down), ?_⟩, fun a ↦ href a.down⟩
        simpa only [Presieve.ofArrows_comp_eq_of_surjective g ULift.down_surjective]
          using hcov
      · intro K V f hc S
        obtain ⟨⟨m, rfl⟩, hV, hcov⟩ := hc
        apply HomologicalComplex.ExactAt.isZero_homology
        apply liftExact S A.X₁.val.presheaf 0
        apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        apply h₁ U m (V ∘ ULift.up) (fun a ↦ f (ULift.up a)) hU
          (fun a ↦ hV (ULift.up a))
        · simpa only [Presieve.ofArrows_comp_eq_of_surjective f ULift.up_surjective]
            using hcov
        · decide
    have hquot (A : ShortComplex (ringedSiteModules.{u} R)) (hA : A.ShortExact)
        (h₁ : P A.X₁) (h₂ : P A.X₂) : P A.X₃ := by
      intro U m V f hU hV hcov S p hp
      have hc' : Presieve.ofArrows (V ∘ (ULift.down : ULift.{u} (Fin m) → Fin m))
          (fun a ↦ f a.down) ∈ J U := by
        simpa only [Presieve.ofArrows_comp_eq_of_surjective f ULift.down_surjective]
          using hcov
      let K' := products U (ULift.{u} (Fin m)) (V ∘ ULift.down)
        (fun a ↦ f a.down) hU (fun a ↦ hV a.down) hc'
      let K := reindexCech K' ULift.up
      have hK : (A.map (T ⋙ K.complexFunctor)).ShortExact := by
        have := hA.mono_f
        apply HomologicalComplex.shortExact_of_degreewise_shortExact
        intro k
        have hs (Z : C) : Function.Exact ((T.map A.f).app (op Z))
            ((T.map A.g).app (op Z)) := by
          exact (ShortComplex.ab_exact_iff_function_exact _).1
            (hA.exact.map_of_mono_of_preservesKernel
              (T ⋙ (evaluation _ _).obj (op Z)) inferInstance inferInstance)
        refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
        · apply (ShortComplex.ab_exact_iff_function_exact _).2
          intro b
          change K.cochainsMap (T.map A.g) k b = 0 ↔
            ∃ a, K.cochainsMap (T.map A.f) k a = b
          constructor
          · intro hb
            have hb' (t : Fin (k + 1) → Fin m) :
                (T.map A.g).app (op (K.W k t)) (b t) = 0 := congrFun hb t
            choose a ha using fun t ↦ (hs (K.W k t) (b t)).1 (hb' t)
            exact ⟨a, funext ha⟩
          · rintro ⟨a, rfl⟩
            funext t
            exact (hs (K.W k t) _).2 ⟨a t, rfl⟩
        · apply (AddCommGrpCat.mono_iff_injective _).2
          intro a b hab
          funext t
          exact (AddCommGrpCat.mono_iff_injective
            ((T.map A.f).app (op (K.W k t)))).1 inferInstance (congrFun hab t)
        · apply (AddCommGrpCat.epi_iff_surjective _).2
          intro b
          choose a ha using fun t ↦ hsurj A hA h₁ (K.W k t)
            (hproducts U (ULift.{u} (Fin m)) (V ∘ ULift.down)
              (fun a ↦ f a.down) hU (fun a ↦ hV a.down) hc' k (ULift.up ∘ t)) (b t)
          exact ⟨a, funext ha⟩
      have h := hK.homology_exact₃ p (p + 1) (by simp)
      have hz : IsZero ((K.cohomologyFunctor p).obj A.X₃.val.presheaf) :=
        h.isZero_X₂_iff.2
          ⟨(h₂ U m V f hU hV hcov K p hp).eq_of_src _ _,
            (h₁ U m V f hU hV hcov K (p + 1) (Nat.zero_lt_succ p)).eq_of_tgt _ _⟩
      obtain ⟨e, _⟩ := K.comparison_exists S
      let i := (Functor.isoWhiskerRight e
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p)).app
          A.X₃.val.presheaf
      exact hz.of_iso i.symm
    intro M hM U hU q hq I
    have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
      SheafOfModules.isGrothendieckAbelian R
    let F := T ⋙ (evaluation _ _).obj (op U)
    have hv : F.rightAcyclic M := by
      apply Functor.rightAcyclic_of_epi_map_g F P ?_ hquot ?_ hM
      · intro N hN W m V f hW hV hc S p hp
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
        apply HomologicalComplex.ExactAt.isZero_homology
        apply unliftExact S N.val.presheaf n
        exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
          (hinj N (V ∘ ULift.down) (fun a ↦ f a.down)
            (reindexCech S ULift.down) (n + 1) (Nat.zero_lt_succ n))
      · intro A hA h₁
        exact (AddCommGrpCat.epi_iff_surjective _).2 (hsurj A hA h₁ U hU)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact (hv n).of_iso (I.isoRightDerivedObj F (n + 1)).symm

end CategoryTheory
