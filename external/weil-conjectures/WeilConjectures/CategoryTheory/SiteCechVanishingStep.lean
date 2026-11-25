/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SiteCechComplex
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

universe u r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The injective-resolution and Čech-complex argument of Stacks 03F9 produces the
base case and the dimension-shifting step. The remaining proof is the standard
strong induction on the degree.

Proof in words: embed a Čech-acyclic sheaf into an injective, use the short exact
section sequences and the long exact sequences of derived functors and Čech
complexes. The injective is Čech-acyclic and has vanishing higher derived
functors; section surjectivity gives degree one, and dimension shifting gives
higher degrees.
(blueprint: lem-weil-pbc-site-cech-vanishing-dimension-shift) -/
theorem siteCech_vanishing_dimension_shift
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{u}]
    [HasExt.{r} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    (B : Set C)
    (Cov : ∀ (U : C) (T : Type u) (V : T → C), (∀ t, V t ⟶ U) → Prop)
    (S : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Cov U T V f → SiteCechComplex V f)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hcover : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
      Cov U T V f → Presieve.ofArrows V f ∈ J U)
    (hB : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (h : Cov U T V f), U ∈ B ∧ (∀ t, V t ∈ B) ∧
        ∀ (p : ℕ) (a : Fin (p + 1) → T), (S U T V f h).W p a ∈ B)
    (hcofinal : ∀ (U : C), U ∈ B →
      ∀ (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U),
        Presieve.ofArrows V f ∈ J U →
        ∃ (K : Type u) (W : K → C) (g : ∀ k, W k ⟶ U),
          Cov U K W g ∧ ∀ k, ∃ (t : T) (a : W k ⟶ V t), a ≫ f t = g k)
    (hcech : ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (h : Cov U T V f) (p : ℕ), 0 < p →
        IsZero (((S U T V f h).cohomologyFunctor p).obj F.obj)) :
    ∀ U, U ∈ B →
      IsZero (H' F 1 U) ∧
        ∀ p, 1 < p → IsZero (H' F (p - 1) U) → IsZero (H' F p U) := by
  classical
  let A (G : Sheaf J.toGrothendieck AddCommGrpCat.{u}) : Prop :=
    ∀ (U : C) (T : Type u) (V : T → C) (f : ∀ t, V t ⟶ U)
      (h : Cov U T V f) (p : ℕ), 0 < p →
        IsZero (((S U T V f h).cohomologyFunctor p).obj G.obj)
  have hsurj (G : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (hG : A G)
      (E : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}))
      (hE : E.ShortExact) (h₁ : E.X₁ = G) (U : C) (hU : U ∈ B) :
      Function.Surjective (E.g.hom.app (Opposite.op U)) := by
    subst h₁
    apply surjective_sections_of_site_cech_h1_vanishing C J E hE U (Cov U)
      (hcover U) (hcofinal U hU)
    intro T V f h K
    obtain ⟨e, _⟩ := (S U T V f h).comparison_exists K
    have ei := (Functor.isoWhiskerRight e
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) 1)).app
        E.X₁.obj
    exact (hG U T V f h 1 (by omega)).of_iso ei.symm
  -- The induction must range over all Čech-acyclic sheaves, including the cokernel.
  have hv (n : ℕ) : ∀ G, A G → ∀ U, U ∈ B → IsZero (H' G (n + 1) U) := by
    induction n with
    | zero =>
        intro G hG U hU
        let E := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
          (cokernel.condition _)
        have hE : E.ShortExact :=
          .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
        let X := (presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj
          (yoneda.obj U ⋙ AddCommGrpCat.free)
        -- Free representables identify degree-zero Ext classes with sections over U.
        let adj := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp
          (sheafificationAdjunction J.toGrothendieck AddCommGrpCat.{u})
        let e (L : Sheaf J.toGrothendieck AddCommGrpCat.{u}) :
            (X ⟶ L) ≃ L.obj.obj (Opposite.op U) :=
          (adj.homEquiv (yoneda.obj U) L).trans yonedaEquiv
        have he {L M : Sheaf J.toGrothendieck AddCommGrpCat.{u}}
            (a : X ⟶ L) (b : L ⟶ M) : e M (a ≫ b) = b.hom.app _ (e L a) := by
          rfl
        apply (AddCommGrpCat.isZero_iff_subsingleton).mpr
        apply subsingleton_of_forall_eq 0
        intro x
        obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ X hE x
          (Abelian.Ext.eq_zero_of_injective _) (zero_add 1)
        obtain ⟨t, ht⟩ := hsurj G hG E hE rfl U hU
          (e E.X₃ (Abelian.Ext.homEquiv₀ y))
        let a := (e E.X₂).symm t
        have ha : a ≫ E.g = Abelian.Ext.homEquiv₀ y := by
          apply (e E.X₃).injective
          rw [he]
          simpa only [a, Equiv.apply_symm_apply] using ht
        have hy : (Abelian.Ext.mk₀ a).comp (Abelian.Ext.mk₀ E.g) (add_zero 0) = y := by
          rw [Abelian.Ext.mk₀_comp_mk₀, ha, Abelian.Ext.mk₀_homEquiv₀_apply]
        rw [← hy, Abelian.Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (zero_add 1),
          hE.comp_extClass, Abelian.Ext.comp_zero]
    | succ n ih =>
        intro G hG U hU
        let E := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
          (cokernel.condition _)
        have hE : E.ShortExact :=
          .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
        have hQ : A E.X₃ := by
          intro V T W f h p hp
          have hI := (site_injective_cech_acyclic W f (hcover V T W f h)
            (S V T W f h) E.X₂).1
          let K := S V T W f h
          let P := E.map (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            K.complexFunctor)
          -- Evaluation is only left exact; surjectivity is supplied on every intersection.
          have hP : P.ShortExact := by
            have := hE.mono_f
            apply HomologicalComplex.shortExact_of_degreewise_shortExact
            intro k
            have hs : ∀ Z : C, Function.Exact (E.f.hom.app (Opposite.op Z))
                (E.g.hom.app (Opposite.op Z)) := by
              intro Z
              let ev := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                (evaluation _ _).obj (Opposite.op Z)
              exact (ShortComplex.ab_exact_iff_function_exact (E.map ev)).mp
                (hE.exact.map_of_mono_of_preservesKernel ev inferInstance inferInstance)
            refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
            · apply (ShortComplex.ab_exact_iff_function_exact _).mpr
              intro b
              change K.cochainsMap E.g.hom k b = 0 ↔
                ∃ a, K.cochainsMap E.f.hom k a = b
              constructor
              · intro hb
                have hb' (a : Fin (k + 1) → T) :
                    E.g.hom.app (Opposite.op (K.W k a)) (b a) = 0 := congrFun hb a
                choose a ha using fun t ↦ (hs (K.W k t) (b t)).mp (hb' t)
                exact ⟨a, funext ha⟩
              · rintro ⟨a, rfl⟩
                funext t
                exact (hs (K.W k t) _).mpr ⟨a t, rfl⟩
            · apply (AddCommGrpCat.mono_iff_injective _).mpr
              intro a b hab
              funext t
              exact (AddCommGrpCat.mono_iff_injective
                (E.f.hom.app (Opposite.op (K.W k t)))).mp
                  inferInstance (congrFun hab t)
            · apply (AddCommGrpCat.epi_iff_surjective _).mpr
              intro b
              choose a ha using fun t ↦ hsurj G hG E hE rfl (K.W k t)
                ((hB V T W f h).2.2 k t) (b t)
              exact ⟨a, funext ha⟩
          have he := hP.homology_exact₃ p (p + 1) rfl
          exact he.isZero_X₂ ((hI p hp).eq_of_src _ _)
            ((hG V T W f h (p + 1) (by omega)).eq_of_tgt _ _)
        have hz := ih E.X₃ hQ U hU
        let X := (presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj
          (yoneda.obj U ⋙ AddCommGrpCat.free)
        have hz' : Subsingleton (Abelian.Ext X E.X₃ (n + 1)) :=
          AddCommGrpCat.subsingleton_of_isZero hz
        apply (AddCommGrpCat.isZero_iff_subsingleton).mpr
        apply subsingleton_of_forall_eq 0
        intro x
        obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ X hE x
          (Abelian.Ext.eq_zero_of_injective _) rfl
        rw [Subsingleton.elim y 0, Abelian.Ext.zero_comp]
  intro U hU
  refine ⟨hv 0 F hcech U hU, ?_⟩
  intro p hp _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (by omega : 0 < p))
  exact hv n F hcech U hU

end CategoryTheory.Sheaf
