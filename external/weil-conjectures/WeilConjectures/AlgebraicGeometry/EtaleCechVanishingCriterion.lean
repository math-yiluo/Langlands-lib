/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.AlgebraicGeometry.EtaleCechSectionwiseShortExact

/-!
# The étale Čech vanishing criterion

Source: Stacks Project, Cohomology on Sites, Lemma 03F9
(blueprint: lem-weil-pbc-cech-vanishing-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Use the standard small model of the étale category, fixing the model universe explicitly.
Source: Mathlib `essentiallySmallSelf`; Stacks 03F9
(blueprint: lem-weil-pbc-cech-vanishing-criterion). -/
local instance etaleSiteEssentiallySmallForCechCriterion (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmallSelf.{0} _

/-- The standard Grothendieck abelian structure supplies injective resolutions without an
extra hypothesis. Source: Mathlib `Sheaf.isGrothendieckAbelian_of_essentiallySmall`; Stacks 03F9
(blueprint: lem-weil-pbc-cech-vanishing-criterion). -/
local instance etaleSheavesGrothendieckForCechCriterion (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1} _ _

/-- Stacks Project, Lemma 03F9 (blueprint: lem-weil-pbc-cech-vanishing-criterion).
Vanishing higher Čech cohomology on a cofinal collection of coverings implies vanishing
higher derived evaluation on every object of the chosen collection `B`. The predicate `Cov`
is membership in the collection of indexed families; `hcover` says they are coverings.
Products in `Over U` are the iterated fibre products over `U`.

Proof (the node's seven steps). Fix `B` and `Cov`, and induct on positive degree, with the
assertion quantified over all Čech-acyclic abelian sheaves (Step 1). Embed such a sheaf `G`
into an injective sheaf `I`, using lem-weil-pbc-module-sheaves-enough-injectives and
def-sp-injective-resolutions; let `Q` be the cokernel (Step 2). Injective sheaves have zero
higher Čech cohomology by lem-weil-pbc-injective-sheaf-cech-acyclic, Stacks 03AW (Step 3).
The cofinality hypothesis and lem-weil-pbc-ses-cech-h1-surjective, Stacks 03F8, give
surjectivity of `I(U) → Q(U)` for `U ∈ B`. Left exact evaluation, or the beginning of
lem-weil-pbc-derived-functor-long-exact and lemma-acyclic-resolutions, gives exactness
of the whole section sequence (Step 4). All intersections belong to `B`, so products of
these short exact sequences give a degreewise short exact sequence of Čech complexes,
using def-weil-pbc-cech-complex and lem-weil-pbc-cochain-complexes-degreewise-exact (Step 5).
Its long exact homology sequence, lem-weil-pbc-complex-ses-homology-long-exact, shows that
`Q` is again Čech-acyclic (Step 6). Finally lem-weil-pbc-derived-functor-long-exact and
lem-weil-pbc-derived-functor-injective-vanishing give zero in degree one by the section
surjectivity, and in each higher degree by dimension shifting to `Q`. Apply the induction
to the originally given `F` (Step 7). -/
theorem isZero_rightDerived_etale_of_cech_vanishing
    (X : Scheme.{u}) (B : Set X.Etale)
    (Cov : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale),
      (∀ i : I, V i ⟶ U) → Prop)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hcover : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), Cov U I V f →
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
    (hB : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), Cov U I V f →
      U ∈ B ∧ (∀ i : I, V i ∈ B) ∧
      ∀ (p : ℕ) (a : Fin (p + 1) → I),
        (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left ∈ B)
    (hcofinal : ∀ (U : X.Etale), U ∈ B →
      ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
        Sieve.ofArrows V f ∈ X.smallEtaleTopology U →
        ∃ (K : Type (u + 1)) (W : K → X.Etale) (g : ∀ k : K, W k ⟶ U),
          Cov U K W g ∧ ∀ k : K, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k)
    (hcech : ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), Cov U I V f → ∀ (p : ℕ), 0 < p →
        IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
          ((Over.forget U).op ⋙ F.obj)).homology p)) :
    ∀ (U : X.Etale), U ∈ B → ∀ (p : ℕ), 0 < p →
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op U)).rightDerived p).obj F) := by
  let P (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
    ∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i, V i ⟶ U), Cov U I V f → ∀ p : ℕ, 0 < p →
        IsZero (((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget U).op ⋙ G.obj)).homology p)
  have hsurj (S : ShortComplex
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (hS : S.ShortExact) (hG : P S.X₁) (U : X.Etale) (hU : U ∈ B) :
      Function.Surjective (S.g.hom.app (op U)) :=
    surjective_sections_of_cech_h1_vanishing X S hS U (Cov U)
      (hcover U) (hcofinal U hU) (fun I V f h ↦ hG U I V f h 1 (by decide))
  have hquot (S : ShortComplex
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (hS : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) : P S.X₃ := by
    intro U I V f hf p hp
    let C := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op ⋙
      cechComplexFunctor (fun i ↦ Over.mk (f i))
    have hC : (S.map C).ShortExact :=
      etale_cech_shortExact_of_sections X S hS U I V f
        (fun n a ↦ hsurj S hS h₁ _ ((hB U I V f hf).2.2 n a))
    have h := hC.homology_exact₃ p (p + 1) (by simp)
    exact h.isZero_X₂_iff.2
      ⟨(h₂ U I V f hf p hp).eq_of_src _ _,
        (h₁ U I V f hf (p + 1) (Nat.zero_lt_succ p)).eq_of_tgt _ _⟩
  have hvan : ∀ q : ℕ, ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      P G → ∀ U : X.Etale, U ∈ B →
        IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
            (op U)).rightDerived (q + 1)).obj G) := by
    intro q
    induction q with
    | zero =>
      intro G hG U hU
      let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op U)
      let S := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)
      have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _)
        inferInstance inferInstance
      obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := hS.exists_rightDerived_δ_exact E 0
      have hepi : Epi (E.map S.g) :=
        (AddCommGrpCat.epi_iff_surjective _).2 (hsurj S hS hG U hU)
      have : Epi ((E.rightDerived 0).map S.g) := by
        rw [← NatIso.naturality_2 E.rightDerivedZeroIsoSelf S.g]
        infer_instance
      exact h₂.isZero_X₂_iff.2 ⟨h₁.epi_f_iff.1 this,
        (E.isZero_rightDerived_obj_injective_succ 0 S.X₂).eq_of_tgt _ _⟩
    | succ q ih =>
      intro G hG U hU
      let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op U)
      let S := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)
      have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _)
        inferInstance inferInstance
      have hI : P S.X₂ := by
        intro W I V f hf p hp
        exact injective_sheaf_cech_acyclic X S.X₂ W I V f (hcover W I V f hf) p hp
      obtain ⟨δ, w₁, w₂, _, h₂⟩ := hS.exists_rightDerived_δ_exact E (q + 1)
      exact h₂.isZero_X₂_iff.2
        ⟨(ih S.X₃ (hquot S hS hG hI) U hU).eq_of_src _ _,
          (E.isZero_rightDerived_obj_injective_succ (q + 1) S.X₂).eq_of_tgt _ _⟩
  intro U hU p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact hvan q F hcech U hU

end AlgebraicGeometry.Scheme
