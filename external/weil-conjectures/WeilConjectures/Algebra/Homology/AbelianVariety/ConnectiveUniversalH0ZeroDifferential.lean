/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.Algebra.Homology.AbelianVariety.UniversalH0SplitDifferential

/-! # Cancelling the degree-zero complement of universal rank-one homology

Source: Stacks Project, Tags 0BCC and 00O0, fixed-affine adaptation.
(blueprint: lem-sc-connective-universal-h0-zero-differential).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- For a connective finite projective complex, universally rank-one zeroth homology
permits cancellation of the complementary degree-zero summand.

Source: Stacks Project, Tags 0BCC and 00O0; degree-zero part of the fixed-affine
normalization argument in lem-sc-universal-h0-projective-normalization.
(blueprint: lem-sc-connective-universal-h0-zero-differential).

Proof: At a prime localize P over A = R_p. Finite projective modules over this
local ring are finite free. Tag 0BCC represents this perfect complex by a finite
free minimal model with ranks equal to its residue homology dimensions. The
ranks vanish outside the finite support bounds, so this model is bounded.
Its negative ranks are zero
because a connective complex remains connective under termwise scalar extension.
Its degree-zero rank is one by the residue test of hzero. Bounded projective
models of the same derived object are homotopy equivalent, and this comparison
remains a homotopy equivalence under any scalar extension. The test
of hzero on A identifies the kernel of the model's differential A -> A^m with A.
Its inclusion into A is multiplication by a non-zero-divisor c. The equation
d(c)=0 forces every coordinate of d(1) to vanish; hence d=0, with no reducedness
assumption. On this model the canonical H0 base-change map to each residue field
is an isomorphism. Transport through the homotopy comparisons shows the same
for the localization of P. Exact localization identifies its H0 with the
localization of H0(P), so the global cycle inclusion has injective reduction
at this prime. The identity test of hzero gives H0(P) isomorphic to R. Since P^(-1)=0,
its canonical cycle inclusion gives j:R -> P^0; its residue extension is
injective at every prime by the base-change comparison. Tag 00O0, finite
presentation, and local-to-global projectivity show that coker(j) is finite
projective and j splits globally. Write P^0 = R plus E using this splitting.
The differential vanishes on R, and its restriction E -> P^1 is injective
at every residue field because the residue kernel is exactly the R summand.
Again Tag 00O0 makes this restriction a split injection with finite projective
cokernel. Cancel the pair E -> image(E) in degrees zero and one using its
inverse as contracting homotopy. The remaining complex has term R in degree
zero, zero outgoing differential, its degree-one term is that cokernel, and
higher terms unchanged. It is bounded, finite projective, and connective.
Projection and inclusion exhibit the homotopy equivalence. Over the zero ring
P itself already has zero differentials. The argument also allows zero higher
terms, including a complex supported only in degree zero. -/
theorem connective_universalH0_zero_differential
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hconnective : ∀ n : ℤ, n < 0 → IsZero (P.X n))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ Q : CochainComplex (ModuleCat.{v} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n)) ∧
      (∀ n : ℤ, Module.Finite R (Q.X n)) ∧
      (∀ n : ℤ, Module.Projective R (Q.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (Q.X n)) ∧
      Q.d 0 1 = 0 ∧ Nonempty (HomotopyEquiv P Q) := by
  classical
  obtain ⟨s, hs⟩ := universalH0_split_differential R P (hf 0) (hf 1) (hp 0) (hp 1)
    (hconnective (-1) (by omega)) hzero
  let h : ∀ i j : ℤ, P.X i ⟶ P.X j := fun i j ↦
    if hi : i = 1 then
      if hj : j = 0 then eqToHom (congrArg P.X hi) ≫ s ≫
        eqToHom (congrArg P.X hj.symm) else 0
    else 0
  let e := Homotopy.nullHomotopicMap h
  have he (n : ℤ) : e.f n =
      P.d n (n + 1) ≫ h (n + 1) n + h n (n - 1) ≫ P.d (n - 1) n := by
    exact Homotopy.nullHomotopicMap_f (by simp) (by simp) h
  have he0 : e.f 0 = P.d 0 1 ≫ s := by simp [he, h]
  have he1 : e.f 1 = s ≫ P.d 0 1 := by simp [he, h]
  have he_other (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : e.f n = 0 := by
    simp [he, h, h1, show n + 1 ≠ 1 by omega]
  have heidem : e ≫ e = e := by
    apply HomologicalComplex.Hom.ext
    apply funext
    intro n
    by_cases h0 : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, he0, Category.assoc]
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ s) hs
    by_cases h1 : n = 1
    · subst n
      simp only [HomologicalComplex.comp_f, he1, Category.assoc]
      rw [hs]
    simp [he_other n h0 h1]
  let p := 𝟙 P - e
  have hp_idem : p ≫ p = p := Idempotents.idem_of_id_sub_idem e heidem
  obtain ⟨Q, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split P p hp_idem
  have hcomponent (n : ℤ) : i.f n ≫ r.f n = 𝟙 (Q.X n) := by
    simpa using congrArg (fun f ↦ f.f n) hir
  have hQzero (n : ℤ) (hn : IsZero (P.X n)) : IsZero (Q.X n) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← hcomponent n, hn.eq_zero_of_tgt (i.f n), zero_comp]
  have hQfinite (n : ℤ) : Module.Finite R (Q.X n) := by
    let := hf n
    apply Module.Finite.of_surjective (r.f n).hom
    intro x
    refine ⟨i.f n x, ?_⟩
    exact congrArg (fun f : Q.X n ⟶ Q.X n ↦ f x) (hcomponent n)
  have hQprojective (n : ℤ) : Module.Projective R (Q.X n) := by
    let := hp n
    apply Module.Projective.of_split (i.f n).hom (r.f n).hom
    exact congrArg ModuleCat.Hom.hom (hcomponent n)
  have hp0 : p.f 0 ≫ P.d 0 1 = 0 := by
    simp only [p, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, he0,
      Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, sub_self]
  have hQd : Q.d 0 1 = 0 := by
    calc
      Q.d 0 1 = Q.d 0 1 ≫ i.f 1 ≫ r.f 1 := by rw [hcomponent 1, Category.comp_id]
      _ = i.f 0 ≫ P.d 0 1 ≫ r.f 1 := by rw [i.comm_assoc]
      _ = i.f 0 ≫ r.f 0 ≫ i.f 0 ≫ P.d 0 1 ≫ r.f 1 := by
        rw [← Category.assoc (i.f 0) (r.f 0), hcomponent 0, Category.id_comp]
      _ = i.f 0 ≫ p.f 0 ≫ P.d 0 1 ≫ r.f 1 := by
        have hr0 : r.f 0 ≫ i.f 0 = p.f 0 :=
          congrArg (fun f ↦ f.f 0) hri
        rw [← Category.assoc (r.f 0), hr0]
      _ = 0 := by rw [← Category.assoc (p.f 0), hp0]; simp
  have hhom : Homotopy p (𝟙 P) := by
    have hz : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
      intro i j hij
      dsimp [h]
      split_ifs with hi hj
      · subst i; subst j
        exact False.elim (hij (by simp))
      all_goals rfl
    refine { hom := fun i j ↦ -h i j
             zero := fun i j hij ↦ by rw [hz i j hij, neg_zero]
             comm := ?_ }
    intro n
    change 𝟙 (P.X n) - (dNext n h + prevD n h) =
      dNext n (-h) + prevD n (-h) + 𝟙 (P.X n)
    rw [map_neg, map_neg]
    abel
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨Q, ⟨a, b, fun n hn ↦ hQzero n (hab n hn)⟩,
    hQfinite, hQprojective, fun n hn ↦ hQzero n (hconnective n hn), hQd, ?_⟩
  exact ⟨{ hom := r
           inv := i
           homotopyHomInvId := (Homotopy.ofEq hri).trans hhom
           homotopyInvHomId := Homotopy.ofEq hir }⟩

end CochainComplex
