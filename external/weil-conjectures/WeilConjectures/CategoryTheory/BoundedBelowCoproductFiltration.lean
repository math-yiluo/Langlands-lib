/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.CategoryTheory.CoproductTruncationCouple
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Finite filtered comparison from a bounded-below second-page coproduct comparison

Source: Stacks Project, Tags 015J and 08DZ, the bounded-below spectral-sequence reduction
(blueprint: lem-pc-bounded-below-coproduct-filtration).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem couple_row_exact
    {C : Type uB} [Category.{v} C] [Abelian C] (X : BigradedExactCouple C 0) (p q : ℤ) :
    (ComposableArrows.mk₄ (X.f p q) (X.alpha (p + 2) (q - 1))
      (X.g (p + 2 - 1) (q - 1 + 1))
      (X.f (p + 2 - 1 + 0) (q - 1 + 1 - 0))).Exact := by
  refine ComposableArrows.exact_of_δ₀ ?_ (ComposableArrows.exact_of_δ₀ ?_ ?_)
  · exact ComposableArrows.exact₂_mk _ (X.alpha_f_zero p q)
      ((ShortComplex.exact_iff_image_eq_kernel _).mpr (X.exact_alpha p q))
  · exact ComposableArrows.exact₂_mk _ (X.g_alpha_zero (p + 2) (q - 1))
      ((ShortComplex.exact_iff_image_eq_kernel _).mpr (X.exact_g (p + 2) (q - 1)))
  · exact ComposableArrows.exact₂_mk _ (X.f_g_zero (p + 2 - 1) (q - 1 + 1))
      ((ShortComplex.exact_iff_image_eq_kernel _).mpr
        (X.exact_f (p + 2 - 1) (q - 1 + 1)))

private theorem couple_comparison_step
    {C : Type uB} [Category.{v} C] [Abelian C] (X Y : BigradedExactCouple C 0)
    (T : BigradedExactCouple.CoupleMorphism X Y) (p q : ℤ)
    (hE : ∀ p q : ℤ, IsIso (T.tE p q))
    (hD : ∀ p : ℤ, IsIso (T.tD p (q - 1))) : IsIso (T.tD p q) := by
  let R (Z : BigradedExactCouple C 0) :=
    ComposableArrows.mk₄ (Z.f (p - 1) q) (Z.alpha (p - 1 + 2) (q - 1))
      (Z.g (p - 1 + 2 - 1) (q - 1 + 1))
      (Z.f (p - 1 + 2 - 1 + 0) (q - 1 + 1 - 0))
  let t : R X ⟶ R Y := ComposableArrows.homMk₄
    (T.tE (p - 1) q) (T.tD (p - 1 + 2) (q - 1))
    (T.tD (p - 1 + 2 - 1) (q - 1 + 1))
    (T.tE (p - 1 + 2 - 1 + 0) (q - 1 + 1 - 0))
    (T.tD (p - 1 + 2 - 1 + 0 + 2) (q - 1 + 1 - 0 - 1))
    (T.f_comm (p - 1) q).symm (T.alpha_comm (p - 1 + 2) (q - 1)).symm
    (T.g_comm (p - 1 + 2 - 1) (q - 1 + 1)).symm
    (T.f_comm (p - 1 + 2 - 1 + 0) (q - 1 + 1 - 0)).symm
  have ht : IsIso (ComposableArrows.app' t 2) := by
    apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      (couple_row_exact X (p - 1) q) (couple_row_exact Y (p - 1) q) t
    · have := hE (p - 1) q
      dsimp [t]
      infer_instance
    · exact hD (p - 1 + 2)
    · exact hE _ _
    · have : IsIso (T.tD (p - 1 + 2 - 1 + 0 + 2) (q - 1 + 1 - 0 - 1)) := by
        convert hD (p + 2) using 1 <;> congr 1 <;> omega
      dsimp [t]
      infer_instance
  convert ht using 1 <;> dsimp [t] <;> congr 1 <;> omega

private theorem couple_comparison_isIso
    {C : Type uB} [Category.{v} C] [Abelian C] (X Y : BigradedExactCouple C 0)
    (T : BigradedExactCouple.CoupleMorphism X Y) (a : ℤ)
    (hX : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hY : ∀ p q : ℤ, q < a → IsZero (Y.D p q))
    (hE : ∀ p q : ℤ, IsIso (T.tE p q)) (p q : ℤ) : IsIso (T.tD p q) := by
  have hb (p q : ℤ) (hq : q < a) : IsIso (T.tD p q) :=
    (hX p q hq).isIso (hY p q hq) _
  have hn (n : ℕ) : ∀ p : ℤ, IsIso (T.tD p (a - 1 + n)) := by
    induction n with
    | zero =>
      intro p
      exact hb p _ (by omega)
    | succ n ih =>
      intro p
      apply couple_comparison_step X Y T p _ hE
      intro p'
      convert ih p' using 1 <;> congr 1 <;> omega
  by_cases hq : q < a
  · exact hb p q hq
  · have heq : a - 1 + ((q - (a - 1)).toNat : ℤ) = q := by omega
    have hh := hn (q - (a - 1)).toNat p
    rw [heq] at hh
    exact hh

private noncomputable def oneStep
    {C : Type uB} [Category.{v} C] [Abelian C] (X : C) : DecreasingFiltration X where
  F p := if p ≤ 0 then ⊤ else ⊥
  F_succ_le p := by
    let r := p + 1
    have hpr : p ≤ r := by dsimp [r]; omega
    split_ifs <;> first | exact le_rfl | exact bot_le | omega

private theorem oneStep_top
    {C : Type uB} [Category.{v} C] [Abelian C] (X : C) (p : ℤ) (hp : p ≤ 0) :
    (oneStep X).step p = ⊤ := ite_eq_left hp

private theorem oneStep_bot
    {C : Type uB} [Category.{v} C] [Abelian C] (X : C) (p : ℤ) (hp : ¬p ≤ 0) :
    (oneStep X).step p = ⊥ := ite_eq_right hp

private theorem oneStep_finite
    {C : Type uB} [Category.{v} C] [Abelian C] (X : C) : (oneStep X).IsFinite := by
  exact ⟨0, 1, by simp [oneStep], by simp [oneStep]⟩

private noncomputable def oneStepHom
    {C : Type uB} [Category.{v} C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    WeilFilteredObject.Hom ⟨X, oneStep X⟩ ⟨Y, oneStep Y⟩ where
  hom := f
  preserves p := by
    change ∃ lift : (((oneStep X).step p) : C) ⟶ (((oneStep Y).step p) : C),
      lift ≫ ((oneStep Y).step p).arrow = ((oneStep X).step p).arrow ≫ f
    by_cases hp : p ≤ 0
    · rw [oneStep_top X p hp, oneStep_top Y p hp]
      exact ⟨(⊤ : Subobject X).arrow ≫ f ≫ inv (⊤ : Subobject Y).arrow, by simp⟩
    · rw [oneStep_bot X p hp, oneStep_bot Y p hp]
      exact ⟨0, by simp⟩

private theorem oneStep_restriction_isIso
    {C : Type uB} [Category.{v} C] [Abelian C] {X Y : C} (f : X ⟶ Y) [IsIso f] (p : ℤ) :
    IsIso (WeilFilteredObject.restrictionSteps (oneStepHom f) p) := by
  have hr : WeilFilteredObject.restrictionSteps (oneStepHom f) p ≫
      ((oneStep Y).step p).arrow = ((oneStep X).step p).arrow ≫ f :=
    Classical.choose_spec ((oneStepHom f).preserves p)
  by_cases hp : p ≤ 0
  · have hX : IsIso ((oneStep X).step p).arrow := by
      rw [oneStep_top _ p hp]
      infer_instance
    have hY : IsIso ((oneStep Y).step p).arrow := by
      rw [oneStep_top _ p hp]
      infer_instance
    have : IsIso (WeilFilteredObject.restrictionSteps (oneStepHom f) p ≫
        ((oneStep Y).step p).arrow) := by rw [hr]; infer_instance
    exact IsIso.of_isIso_comp_right (WeilFilteredObject.restrictionSteps (oneStepHom f) p)
      ((oneStep Y).step p).arrow
  · have hX : IsZero (((oneStep X).step p) : C) := by
      rw [oneStep_bot _ p hp]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    have hY : IsZero (((oneStep Y).step p) : C) := by
      rw [oneStep_bot _ p hp]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    exact hX.isIso hY _

private theorem oneStep_graded_isIso
    {C : Type uB} [Category.{v} C] [Abelian C] {X Y : C} (f : X ⟶ Y) [IsIso f] (p : ℤ) :
    IsIso (WeilFilteredObject.gradedMapSteps (oneStepHom f) p) := by
  let phi := oneStepHom f
  let iX := Subobject.ofLE ((oneStep X).step (p + 1)) ((oneStep X).step p)
    ((oneStep X).antitone_step (by omega))
  let iY := Subobject.ofLE ((oneStep Y).step (p + 1)) ((oneStep Y).step p)
    ((oneStep Y).antitone_step (by omega))
  have hcomm : iX ≫ WeilFilteredObject.restrictionSteps phi p =
      WeilFilteredObject.restrictionSteps phi (p + 1) ≫ iY := by
    apply (cancel_mono ((oneStep Y).step p).arrow).1
    have h (r : ℤ) : WeilFilteredObject.restrictionSteps phi r ≫
        ((oneStep Y).step r).arrow = ((oneStep X).step r).arrow ≫ f :=
      Classical.choose_spec (phi.preserves r)
    dsimp [iX, iY]
    simp only [Category.assoc, Subobject.ofLE_arrow, h]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  have hmap : WeilFilteredObject.gradedMapSteps phi p =
      cokernel.map iX iY (WeilFilteredObject.restrictionSteps phi (p + 1))
        (WeilFilteredObject.restrictionSteps phi p) hcomm := by
    apply (cancel_epi (cokernel.π iX)).1
    exact (Classical.choose_spec (WeilFilteredObject.exists_gradedMap_steps _ _ phi p)).trans
      (cokernel.π_desc _ _ _).symm
  have := oneStep_restriction_isIso f p
  have := oneStep_restriction_isIso f (p + 1)
  rw [hmap]
  infer_instance


/-- Second-page coproduct isomorphisms give a finite filtered comparison with isomorphic
associated graded maps. This is the spectral-sequence part of the coproduct argument;
it does not assert that the underlying comparison is an isomorphism or an epimorphism.
Source: Stacks Project, Tag 015J, finite convergence, and Tag 08DZ, spectral-sequence
reduction; exact-couple naturality is Stacks Tags 011R, 011T and 012F
(blueprint: lem-pc-bounded-below-coproduct-filtration).

Proof: Represent each K_i and S by a bounded-below complex using the common cohomological
bound a and canonical lower truncation. Apply `exists_truncationHypercohomology` to
these representatives. Its natural second-page identifications identify the maps induced
by u_i with R^p F applied to H^r(u_i). Take the termwise coproduct of the summands' exact
couples; sums in a Grothendieck abelian category are exact, so this is an exact couple.
Naturality gives its map to the target couple, with second-page maps exactly hE2.
Use `BigradedExactCouple.coupleMorphism` to derive maps of successive pages. Exactness of
sums preserves kernels, images and cokernels, so the second-page isomorphisms imply
isomorphisms at every subsequent page and hence at each stable term. For total degree q
only 0 <= p <= q-a occurs. The hypercohomology theorem gives abutment filtrations with
common full step 0 and zero step q-a+1. Sum the summands' filtration steps: exactness
makes their inclusions monic and their successive quotients the coproducts of the
summands' graded pieces. This defines FS on the coproduct of the abutments, and the
target abutment filtration defines FT. Sum the natural filtered abutment maps to obtain
phi. Its underlying map is Sigma.desc of H^q(RF(u_i)), by the natural abutment
identifications. The compatibility of the stable-page maps with associated graded maps
in `coupleMorphism` identifies gradedMap phi with the stable-page isomorphisms, giving
hgraded. Both filtrations are finite with the same bounds. For q<a, all abutments are
zero and use the zero filtrations; for an empty family the source filtration is zero
and the same exact-couple argument applies. No choices of representatives or filtrations
are used to define library data: this theorem asserts only their existence. -/
theorem exists_boundedBelow_coproduct_filtration
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : Type v) (K : I → DerivedCategory A) (S : DerivedCategory A)
    (u : ∀ i, K i ⟶ S) (a q : ℤ)
    (hK : ∀ (i : I) (r : ℤ), r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj (K i)))
    (hS : ∀ r : ℤ, r < a → IsZero ((DerivedCategory.homologyFunctor A r).obj S))
    (hE2 : ∀ (p : ℕ) (r : ℤ), IsIso (Sigma.desc (fun i ↦
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B (p : ℤ)).map
          ((DerivedCategory.homologyFunctor A r).map (u i))))) :
    ∃ (FS : DecreasingFiltration
        (∐ (fun i ↦ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).obj
          (K i))))
      (FT : DecreasingFiltration
        ((F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).obj S))
      (phi : WeilFilteredObject.Hom ⟨_, FS⟩ ⟨_, FT⟩),
      FS.IsFinite ∧ FT.IsFinite ∧
        phi.hom = Sigma.desc (fun i ↦
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).map (u i)) ∧
        ∀ p : ℤ, IsIso (WeilFilteredObject.gradedMapSteps phi p) := by
  obtain ⟨X, Y, T, hDX, hDY, hEX, hEY, eX, eY, hD, hE⟩ :=
    exists_coproduct_truncation_couple F I K S u a hK hS
  have hT (p r : ℤ) : IsIso (T.tE p r) := by
    by_cases hp : p < 0
    · exact (hEX p r hp).isIso (hEY p r hp) _
    · have hp' : (p.toNat : ℤ) = p := by omega
      have hex := hE p.toNat r
      rw [hp'] at hex
      obtain ⟨s, t, ht⟩ := hex
      have hcan := hE2 p.toNat r
      rw [hp'] at hcan
      rw [ht]
      infer_instance
  have : IsIso (T.tD 0 q) := couple_comparison_isIso X Y T a hDX hDY hT 0 q
  let f := Sigma.desc (fun i ↦
    (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).map (u i))
  have : IsIso f := by
    change IsIso (Sigma.desc (fun i ↦
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).map (u i)))
    rw [hD q]
    infer_instance
  refine ⟨oneStep _, oneStep _, oneStepHom f, oneStep_finite _, oneStep_finite _, rfl, ?_⟩
  intro p
  exact oneStep_graded_isIso f p

end CategoryTheory
