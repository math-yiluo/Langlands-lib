/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.CommRingCat
import WeilConjectures.Mathlib.RingTheory.LocalRing.Basic

/-! # Clopen subsets and idempotent global functions of schemes

Source: Stacks Project, Algebra, Lemma 10.21.3 (Tag 00EE,
`lemma-disjoint-decomposition`), the affine case; the scheme case follows by the sheaf
property, as in Schemes, Tag 01I5, proof of `lemma-disjoint-union-affines`.
(blueprint: lem-weil-pbc-scheme-clopen-idempotent)

## Main statements

* `scheme_clopen_idempotent`: the clopen correspondence and its pullback compatibility.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The locus where a global function has nonzero germ, used for the idempotent
correspondence of Stacks Project, Algebra, Tag 00EE (`lemma-disjoint-decomposition`).
(blueprint: lem-weil-pbc-scheme-clopen-idempotent) -/
def idempotentOpen {X : Scheme.{u}} (e : Γ(X, ⊤)) : Set X :=
  {x | X.presheaf.Γgerm x e ≠ 0}

/-- (blueprint: lem-weil-pbc-scheme-clopen-idempotent) Let `X` be a scheme. For every
idempotent global section `e`, the set of points where its germ is nonzero equals the
locus where its germ is one and is clopen, with complementary locus for `1 - e`.
Idempotents and clopen opens are bijective, with inverse given by the section restricting
to one and zero on the two complementary opens. Pullback of an idempotent locus is
its inverse image under a scheme morphism.

Source: Stacks Project, Algebra, Tag 00EE (`lemma-disjoint-decomposition`), extended
from affine schemes by the sheaf property (Schemes, Tag 01I5, proof).

Proof, following the node's five steps:
1. Germ maps are ring homomorphisms, so every germ of an idempotent is idempotent.
   Stalks are local rings (`def-pc-scheme`); by
   `lem-weil-pbc-local-ring-idempotent-zero-one`, these germs are zero or one.
   Thus the nonzero-germ locus is the one-germ locus and the basic open of the section
   (`lem-weil-pbc-basic-open-function`).
2. The basic open is open. The section `1 - e` is idempotent, and its germs are the
   complements of the germs of `e`. Its locus is exactly the complementary set,
   also open, proving closedness of the original locus.
3. Equal loci give equal germs, since idempotent germs are zero or one. The sheaf
   property, `lem-weil-pbc-sheaf-sections-determined-by-germs`, gives equal sections,
   proving injectivity.
4. For a clopen `U`, use `lem-weil-pbc-sheaf-disjoint-union-product` to identify
   global sections with sections on `U` times sections on its complement. The inverse
   image of `(1, 0)` is unique, is idempotent, and has locus `U`, proving surjectivity
   and describing the inverse. This also works for an empty open, whose ring is zero.
   Restriction values and the displayed germ values are equivalent by sheaf extensionality.
5. Pullback on global sections is a ring homomorphism, so it preserves idempotence.
   Apply `lem-weil-pbc-basic-open-pullback` to the basic opens identified in step 1
   to obtain the inverse-image equality. -/
theorem scheme_clopen_idempotent (X : Scheme.{u}) :
    (∀ (e : Γ(X, ⊤)), IsIdempotentElem e →
      idempotentOpen e = {x : X | X.presheaf.Γgerm x e = 1} ∧
      IsOpen (idempotentOpen e) ∧
      IsClosed (idempotentOpen e) ∧
      idempotentOpen (1 - e) = (idempotentOpen e)ᶜ) ∧
    (Function.Injective (fun (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) ↦
      idempotentOpen e.1) ∧
      (∀ (U : Set X), IsOpen U ∧ IsClosed U → ∃ e : Γ(X, ⊤),
        IsIdempotentElem e ∧ idempotentOpen e = U)) ∧
    (∀ (U : {U : Set X // IsOpen U ∧ IsClosed U}), ∃! (e : Γ(X, ⊤)),
      IsIdempotentElem e ∧
      (∀ x : X, x ∈ U.1 → X.presheaf.Γgerm x e = 1) ∧
      (∀ x : X, x ∉ U.1 → X.presheaf.Γgerm x e = 0)) ∧
    (∀ {Y : Scheme.{u}} (g : Y ⟶ X) (e : Γ(X, ⊤)), IsIdempotentElem e →
      IsIdempotentElem (g.appTop e) ∧
      idempotentOpen (g.appTop e) = g.base ⁻¹' idempotentOpen e) := by
  classical
  have ext (a b : Γ(X, ⊤))
      (h : ∀ x, X.presheaf.Γgerm x a = X.presheaf.Γgerm x b) : a = b :=
    TopCat.Presheaf.section_ext X.sheaf ⊤ a b fun x _ ↦ h x
  have values {Z : Scheme.{u}} (e : Γ(Z, ⊤)) (he : IsIdempotentElem e) (x : Z) :
      Z.presheaf.Γgerm x e = 0 ∨ Z.presheaf.Γgerm x e = 1 :=
    IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
      (he.map (Z.presheaf.Γgerm x).hom)
  have basic {Z : Scheme.{u}} (e : Γ(Z, ⊤)) (he : IsIdempotentElem e) :
      idempotentOpen e = (Z.basicOpen e : Set Z) := by
    ext x
    rw [SetLike.mem_coe, Scheme.mem_basicOpen_top]
    change (Z.presheaf.Γgerm x e ≠ 0) ↔ IsUnit (Z.presheaf.Γgerm x e)
    rcases values e he x with h | h <;> simp [h]
  have locus (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
      idempotentOpen e = {x : X | X.presheaf.Γgerm x e = 1} := by
    ext x
    rcases values e he x with h | h <;> simp [idempotentOpen, h]
  have inj : Function.Injective
      (fun (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) ↦ idempotentOpen e.1) := by
    intro e f h
    apply Subtype.ext
    apply ext
    intro x
    have hx := Set.ext_iff.mp h x
    change (X.presheaf.Γgerm x e.1 ≠ 0 ↔ X.presheaf.Γgerm x f.1 ≠ 0) at hx
    rcases values e.1 e.2 x with he | he <;>
      rcases values f.1 f.2 x with hf | hf
    · exact he.trans hf.symm
    · exact False.elim ((hx.mpr (hf ▸ one_ne_zero)) (he ▸ rfl))
    · exact False.elim ((hx.mp (he ▸ one_ne_zero)) (hf ▸ rfl))
    · exact he.trans hf.symm
  have exists_section (S : Set X) (hS : IsOpen S ∧ IsClosed S) :
      ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
        (∀ x : X, X.presheaf.Γgerm x e = if x ∈ S then 1 else 0) := by
    let U : X.Opens := ⟨S, hS.1⟩
    let V : X.Opens := ⟨Sᶜ, hS.2.isOpen_compl⟩
    have hUV : U ⊔ V = ⊤ := by ext x; simp [U, V]
    have hUV' : U ⊓ V = ⊥ := by ext x; simp [U, V]
    let s : Γ(X, U ⊔ V) := (X.sheaf.objSupIsoProdEqLocus U V).inv ⟨(1, 0),
      TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx ↦ by
        rw [hUV'] at hx; exact absurd hx (by simp)⟩
    let e : Γ(X, ⊤) := X.presheaf.map (eqToHom hUV.symm).op s
    have hsU : X.presheaf.map (homOfLE le_sup_left).op s = 1 :=
      X.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have hsV : X.presheaf.map (homOfLE le_sup_right).op s = 0 :=
      X.sheaf.objSupIsoProdEqLocus_inv_snd U V _
    have heU : X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op e = 1 := by
      rw [← hsU, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have heV : X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op e = 0 := by
      rw [← hsV, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    have hgerm (x : X) : X.presheaf.Γgerm x e = if x ∈ S then 1 else 0 := by
      change X.presheaf.germ ⊤ x trivial e = if x ∈ S then 1 else 0
      split_ifs with hx
      · rw [← X.presheaf.germ_res (homOfLE le_top : U ⟶ ⊤) x hx,
          CommRingCat.comp_apply, heU, map_one]
      · rw [← X.presheaf.germ_res (homOfLE le_top : V ⟶ ⊤) x hx,
          CommRingCat.comp_apply, heV, map_zero]
    refine ⟨e, ?_, hgerm⟩
    apply ext
    intro x
    rw [map_mul, hgerm]
    split_ifs <;> simp
  refine ⟨?_, ⟨inj, ?_⟩, ?_, ?_⟩
  · intro e he
    have hc : idempotentOpen (1 - e) = (idempotentOpen e)ᶜ := by
      ext x
      change (X.presheaf.Γgerm x (1 - e) ≠ 0) ↔ ¬(X.presheaf.Γgerm x e ≠ 0)
      rw [map_sub, map_one]
      rcases values e he x with h | h <;> simp [h]
    have ho : IsOpen (idempotentOpen e) := (basic e he).symm ▸ (X.basicOpen e).isOpen
    have ho' : IsOpen (idempotentOpen (1 - e)) :=
      (basic (1 - e) he.one_sub).symm ▸ (X.basicOpen (1 - e)).isOpen
    exact ⟨locus e he, ho, isOpen_compl_iff.mp (hc ▸ ho'), hc⟩
  · intro S hS
    obtain ⟨e, he, hg⟩ := exists_section S hS
    refine ⟨e, he, ?_⟩
    ext x
    simp only [idempotentOpen, Set.mem_ofPred_eq, hg]
    split_ifs with hx <;> simp [hx]
  · intro U
    obtain ⟨e, he, hg⟩ := exists_section U.1 U.2
    refine ⟨e, ⟨he, ?_, ?_⟩, ?_⟩
    · intro x hx
      simp [hg, hx]
    · intro x hx
      simp [hg, hx]
    · intro f hf
      apply ext
      intro x
      by_cases hx : x ∈ U.1
      · rw [hf.2.1 x hx, hg, ite_eq_left hx]
      · rw [hf.2.2 x hx, hg, ite_eq_right hx]
  · intro Y g e he
    have hp : IsIdempotentElem (g.appTop e) := he.map g.appTop.hom
    refine ⟨hp, ?_⟩
    rw [basic _ hp, basic _ he]
    exact congrArg (fun U : Y.Opens ↦ (U : Set Y))
      (Scheme.preimage_basicOpen_top g e).symm


end AlgebraicGeometry
