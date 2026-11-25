/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-!
# The Čech vanishing criterion for module sheaves

Source: Stacks Project, Cohomology of Sheaves, Tags 01EV and 01E1 (2)
(blueprint: lem-weil-pbc-module-cech-vanishing-criterion).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Vanishing of positive Čech cohomology for every covering of every open implies
vanishing of positive derived module cohomology on every open subscheme.
The products in `SiteCechComplex` on the poset of opens are uniquely the finite
intersections, and its index maps are the omitted-factor inclusions. Quantifying over
all choices therefore expresses the same hypothesis as the intersection Čech complex.

Source: Stacks Project, Cohomology of Sheaves, Tags 01EV and 01E1 (2)
(blueprint: lem-weil-pbc-module-cech-vanishing-criterion).

Proof (the nine steps of the node):
1. Induct on positive degree, simultaneously for all Čech-acyclic module sheaves.
2. Embed such a sheaf G into an injective I and take its cokernel Q, using
   lem-weil-pbc-scheme-modules-enough-injectives, def-sp-injective-resolutions and
   def-weil-pbc-exact-sequence in the abelian module category.
3. I is Čech-acyclic by lem-weil-pbc-module-injective-open-cover-cech-acyclic (01EP).
4. Kernels are sectionwise. Apply lem-weil-pbc-module-ses-cech-h1-surjective (01EU)
   to all coverings of each open W: vanishing Čech H¹(G) makes I(W) → Q(W) surjective.
   Thus the sequence is short exact as presheaves, not just as sheaves.
5. Taking products of these sectionwise short exact sequences on the intersections
   gives a short exact sequence of Čech complexes (def-weil-pbc-site-cech-complex and
   lem-weil-pbc-cochain-complexes-degreewise-exact).
6. Its long exact cohomology sequence, lem-weil-pbc-complex-ses-homology-long-exact,
   places positive Čech Hᵖ(Q) between zero groups Hᵖ(I) and Hᵖ⁺¹(G). Hence Q is
   again Čech-acyclic.
7. Restrict the short exact sequence to U. Restriction is exact and preserves injectives
   by lem-weil-pbc-module-open-restriction-injectives (01E1); its sections agree with
   the original sections on U by lem-weil-pbc-module-restriction-open-immersion-colimits.
8. By pqf-def-cohomology and def-sp-left-exact-additive, cohomology of U is derived
   global sections in modules, computed with injective resolutions.
9. Apply lem-weil-pbc-derived-functor-long-exact to the restricted sequence. Positive
   cohomology of I vanishes by lem-weil-pbc-derived-functor-injective-vanishing (015B).
   In degree one, R⁰Γ ≅ Γ (lem-weil-pbc-right-derived-universal-delta-functor) and
   surjectivity in step 4 imply H¹(G) = 0. In higher degrees the induction hypothesis
   for Q from step 6 and the exact sequence imply Hᵖ(G) = 0. Apply this to F. -/
theorem module_cohomology_isZero_of_cech_vanishing (X : Scheme.{u}) (F : X.Modules)
    (hcech : ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens)
      (hom : ∀ i, V i ⟶ U), (⨆ i, V i) = U →
      ∀ (S : SiteCechComplex V hom) (p : ℕ), 0 < p →
        IsZero ((S.cohomologyFunctor p).obj ((toPresheaf X).obj F))) :
    ∀ (U : X.Opens) (p : ℕ), 0 < p →
      IsZero ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
        ((restrictFunctor U.ι).obj F)) := by
  classical
  let : EnoughInjectives X.Modules := inferInstance
  let : Preadditive (TopCat.Presheaf AddCommGrpCat.{u} X) :=
    inferInstanceAs (Preadditive (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
  let : Abelian (TopCat.Presheaf AddCommGrpCat.{u} X) :=
    inferInstanceAs (Abelian (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
  let : (toPresheaf X).Additive :=
    inferInstanceAs ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).Additive)
  let T : X.Modules ⥤ (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) := toPresheaf X
  let : T.Additive := inferInstanceAs ((toPresheaf X).Additive)
  let : PreservesLimits T := inferInstanceAs (PreservesLimits (toPresheaf X))
  let P (G : X.Modules) : Prop :=
    ∀ (U : X.Opens) (I : Type (max u w)) (V : I → X.Opens)
      (hom : ∀ i, V i ⟶ U), (⨆ i, V i) = U →
      ∀ (C : SiteCechComplex V hom) (p : ℕ), 0 < p →
        IsZero ((C.cohomologyFunctor p).obj ((toPresheaf X).obj G))
  have hsurj (S : ShortComplex X.Modules) (hS : S.ShortExact) (hG : P S.X₁)
      (U : X.Opens) : Function.Surjective (S.g.val.app (Opposite.op U)) := by
    apply Scheme.module_sections_surjective_of_cech_h1_vanishing X S hS U
      (fun I V _ ↦ (⨆ i : I, V i) = U)
    · intro I V hV hcover x hx
      rw [← hcover] at hx
      exact TopologicalSpace.Opens.mem_iSup.mp hx
    · intro I V hV hcover
      refine ⟨I, V, hV, ?_, fun i ↦ ⟨i, le_rfl⟩⟩
      apply le_antisymm (iSup_le hV)
      intro x hx
      obtain ⟨i, hi⟩ := hcover x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
    · intro I V hV hcover hom C
      exact hG U I V hom hcover C 1 (by decide)
  have hquot (S : ShortComplex X.Modules) (hS : S.ShortExact)
      (h₁ : P S.X₁) (h₂ : P S.X₂) : P S.X₃ := by
    intro U I V hom hcover C p hp
    have : Mono S.f := hS.mono_f
    have hA : (S.map T).ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · exact hS.exact.map_of_mono_of_preservesKernel T inferInstance inferInstance
      · change Mono (T.map S.f)
        infer_instance
      · have (W : X.Opensᵒᵖ) : Epi ((S.map T).g.app W) :=
          (AddCommGrpCat.epi_iff_surjective _).mpr (hsurj S hS h₁ W.unop)
        exact NatTrans.epi_of_epi_app _
    let K : (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        CochainComplex AddCommGrpCat.{max u w} ℕ := C.complexFunctor
    have hC : ((S.map T).map K).ShortExact := by
      apply HomologicalComplex.shortExact_of_degreewise_shortExact
      intro n
      have : Mono (S.map T).f := hA.mono_f
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · apply (ShortComplex.ab_exact_iff_function_exact _).mpr
        exact C.degreewise_exact _ hA.exact n
      · apply (AddCommGrpCat.mono_iff_injective _).mpr
        intro a b hab
        funext t
        exact (AddCommGrpCat.mono_iff_injective
          ((T.map S.f).app (Opposite.op (C.W n t)))).mp
            inferInstance (congrFun hab t)
      · apply (AddCommGrpCat.epi_iff_surjective _).mpr
        intro a
        choose b hb using fun t ↦ hsurj S hS h₁ (C.W n t) (a t)
        exact ⟨b, funext hb⟩
    have h := hC.homology_exact₃ p (p + 1) (by simp)
    exact h.isZero_X₂_iff.mpr
      ⟨(h₂ U I V hom hcover C p hp).eq_of_src _ _,
        (h₁ U I V hom hcover C (p + 1) (Nat.zero_lt_succ p)).eq_of_tgt _ _⟩
  have hrestrict (U : X.Opens) :
      (∀ (S : ShortComplex X.Modules), S.ShortExact →
        (S.map (restrictFunctor U.ι)).ShortExact) ∧
      (∀ (I : X.Modules), Injective I → Injective ((restrictFunctor U.ι).obj I)) := by
    let O := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
    let R := restrictFunctor U.ι
    let : O.Additive := (module_open_restriction_injectives X U).1
    let : R.Additive := ⟨by intros; rfl⟩
    have hO := (module_open_restriction_injectives X U).2.1
    let : O.PreservesMonomorphisms := Functor.preservesMonomorphisms_of_map_exact O hO
    let : O.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_map_exact O hO
    constructor
    · intro S hS
      have : Mono S.f := hS.mono_f
      have : Epi S.g := hS.epi_g
      have hSO : (S.map O).ShortExact :=
        { exact := hO S hS.exact
          mono_f := by change Mono (O.map S.f); infer_instance
          epi_g := by change Epi (O.map S.g); infer_instance }
      have hSOE := hSO.map_of_exact (overEquiv U).functor
      apply ShortComplex.shortExact_of_iso (S.mapNatIso (overFunctorEquiv U))
      exact hSOE
    · intro I hI
      let : Injective (O.obj I) := (module_open_restriction_injectives X U).2.2.1 I hI
      have h := (overEquiv U).map_injective_iff (O.obj I)
      have h' : Injective ((overEquiv U).functor.obj (O.obj I)) := h.mpr inferInstance
      exact Injective.of_iso ((overFunctorEquiv U).app I) h'
  have hvan : ∀ q : ℕ, ∀ G : X.Modules, P G → ∀ U : X.Opens,
      IsZero ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace (q + 1)).obj
        ((restrictFunctor U.ι).obj G)) := by
    intro q
    induction q with
    | zero =>
      intro G hG U
      let S := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)
      have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _)
        inferInstance inferInstance
      let E := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
      let : PreservesFiniteLimits E :=
        inferInstanceAs (PreservesFiniteLimits
          (SheafOfModules.evaluation (moduleRings U.toScheme.toRingedSpace)
            (Opposite.op ⊤)))
      let R := restrictFunctor U.ι
      let : R.Additive := ⟨by intros; rfl⟩
      have hRS := (hrestrict U).1 S hS
      let : EnoughInjectives U.toScheme.Modules := inferInstance
      let : Injective (R.obj S.X₂) := (hrestrict U).2 S.X₂ inferInstance
      obtain ⟨δ, _, hall⟩ := hRS.exists_rightDerived_full_long_exact E
      obtain ⟨_, w₁, w₂, h₁, h₂⟩ := hall 0
      have hepi : Epi (E.map (R.map S.g)) := by
        apply (ModuleCat.epi_iff_surjective _).mpr
        change Function.Surjective (S.g.val.app (Opposite.op (U.ι ''ᵁ ⊤)))
        exact hsurj S hS hG _
      have hepi' : Epi ((E.rightDerived 0).map (R.map S.g)) := by
        rw [← NatIso.naturality_2 E.rightDerivedZeroIsoSelf (R.map S.g)]
        infer_instance
      exact h₂.isZero_X₂_iff.mpr ⟨h₁.epi_f_iff.mp hepi',
        (E.isZero_rightDerived_obj_injective_succ 0 (R.obj S.X₂)).eq_of_tgt _ _⟩
    | succ q ih =>
      intro G hG U
      let S := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)
      have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _)
        inferInstance inferInstance
      have hI : P S.X₂ := by
        intro W I V hom hcover C p hp
        exact module_injective_open_cover_cech_acyclic S.X₂ W I V
          (fun i ↦ leOfHom (hom i)) hcover C p hp
      let E := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
      let : PreservesFiniteLimits E :=
        inferInstanceAs (PreservesFiniteLimits
          (SheafOfModules.evaluation (moduleRings U.toScheme.toRingedSpace)
            (Opposite.op ⊤)))
      let R := restrictFunctor U.ι
      let : R.Additive := ⟨by intros; rfl⟩
      have hRS := (hrestrict U).1 S hS
      let : EnoughInjectives U.toScheme.Modules := inferInstance
      let : Injective (R.obj S.X₂) := (hrestrict U).2 S.X₂ inferInstance
      obtain ⟨δ, _, hall⟩ := hRS.exists_rightDerived_full_long_exact E
      obtain ⟨_, w₁, w₂, _, h₂⟩ := hall (q + 1)
      exact h₂.isZero_X₂_iff.mpr
        ⟨(ih S.X₃ (hquot S hS hG hI) U).eq_of_src _ _,
          (E.isZero_rightDerived_obj_injective_succ (q + 1) (R.obj S.X₂)).eq_of_tgt _ _⟩
  intro U p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact hvan q F hcech U

end AlgebraicGeometry.Scheme.Modules
