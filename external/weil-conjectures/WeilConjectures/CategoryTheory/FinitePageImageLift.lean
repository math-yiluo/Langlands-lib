/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.DerivedCoupleExact

/-!
# Incoming-alpha image lifts to derived-D terms

Source: Stacks Tags 011S and 0AMJ; blueprint lemma-uniform-bound-proper-direct-image--1, step 5.
(blueprint: lem-sp-finite-page-image-lift)
-/

@[expose] public section

universe u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem incomingAlphaIter_succ
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℕ) (p q : ℤ) :
    X.incomingAlphaIter (n + 1) p q =
      X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
        eqToHom (by congr 1 <;> omega) ≫ X.incomingAlphaIter n p q := by
  apply eq_of_heq
  dsimp [BigradedExactCouple.incomingAlphaIter, BigradedExactCouple.alphaIter]
  simp only [Category.assoc]
  apply heq_comp rfl rfl rfl HEq.rfl
  simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  rw [heq_eqToHom_comp_iff]
  congr! 1 <;> omega

private theorem prescribed_inclusion_images
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0)
    (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (hinc0 : ∀ p q : ℤ, inc 0 p q = 𝟙 _)
    (hinc : ∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q) :
    (∀ (r : ℕ) (p q : ℤ), Mono (inc r p q)) ∧
    (∀ (r : ℕ) (p q : ℤ), imageSubobject (inc r p q) =
      imageSubobject (X.incomingAlphaIter r p q)) := by
  obtain ⟨A, I, hA0, hAs, hI0, hIs, hImono, hIm, _, _⟩ := X.pageCouple_image
  have hA : ∀ (r : ℕ) (p q : ℤ), A r p q = X.incomingAlphaIter r p q := by
    intro r p q
    induction r with
    | zero =>
      rw [hA0]
      simp only [BigradedExactCouple.incomingAlphaIter,
        BigradedExactCouple.alphaIter, eqToHom_trans]
    | succ r ih => rw [hAs, ih, incomingAlphaIter_succ]
  have hI : ∀ (r : ℕ) (p q : ℤ), I r p q = inc r p q := by
    intro r p q
    induction r with
    | zero => rw [hI0, hinc0]; rfl
    | succ r ih => rw [hIs, hinc, ih]
  refine ⟨?_, ?_⟩
  · intro r p q
    rw [← hI]
    exact hImono r p q
  · intro r p q
    rw [← hI, hIm, hA]

private theorem alphaIter_add_heq
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (r s : ℕ) (p q : ℤ) :
    X.alphaIter (r + s) p q ≍ X.alphaIter r p q ≫
      X.alphaIter s (p - r) (q + r) := by
  induction r generalizing p q with
  | zero =>
    simp only [BigradedExactCouple.alphaIter, heq_eqToHom_comp_iff]
    congr! 1 <;> omega
  | succ r ih =>
    have hn : X.alphaIter (r + 1 + s) p q ≍ X.alphaIter ((r + s) + 1) p q := by
      congr! 1
      omega
    apply hn.trans
    simp only [BigradedExactCouple.alphaIter]
    simp only [Category.assoc]
    apply heq_comp rfl rfl (by congr 1 <;> omega) HEq.rfl
    simp only [← Category.assoc, comp_eqToHom_heq_iff]
    have hshift : X.alphaIter s (p - 1 - r) (q + 1 + r) ≍
        X.alphaIter s (p - (r + 1 : ℕ)) (q + (r + 1 : ℕ)) := by
      congr! 1 <;> omega
    have := ih (p - 1) (q + 1)
    apply this.trans
    simp only [Category.assoc]
    apply heq_comp rfl rfl (by congr 1 <;> omega) HEq.rfl
    rw [heq_eqToHom_comp_iff]
    exact hshift

private theorem incoming_split_heq
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (r p : ℕ) (q : ℤ) (hp : p ≤ r) :
    X.incomingAlphaIter r ((p : ℤ) - r) (q + r) ≍
      X.incomingAlphaIter p 0 (p + q) ≫ X.alphaIter (r - p) 0 (p + q) := by
  unfold BigradedExactCouple.incomingAlphaIter
  apply (comp_eqToHom_heq _ _).trans
  have hn : X.alphaIter r ((p : ℤ) - r + r) (q + r - r) ≍
      X.alphaIter (p + (r - p)) (p : ℤ) q := by
    congr! 1 <;> omega
  apply hn.trans
  apply (alphaIter_add_heq X p (r - p) p q).trans
  simp only [Category.assoc]
  apply heq_comp (by congr 1 <;> omega) (by congr 1 <;> omega)
    (by congr 1 <;> omega)
  · congr! 1 <;> omega
  · rw [heq_eqToHom_comp_iff]
    congr! 1 <;> omega

/-- The incoming-alpha filtration step lifts isomorphically to the derived-D term.
Source: blueprint lemma-uniform-bound-proper-direct-image--1, proof step 5; Stacks Tags 011S and
0AMJ. (blueprint: lem-sp-finite-page-image-lift)

Proof: Put R=max(p+3,q-a+2), r=R-2, u=p-r and v=q+r. First identify the families
A and I in pageCouple_image with incomingAlphaIter and inc. Their initial values
and successor recurrences determine both families uniquely by natural-number
induction. The recurrence for incomingAlphaIter follows by expanding alphaIter
and comparing the index transports. Thus inc r u v is monomorphic and its image
is the incoming r-fold alpha image. Induction on the first number of iterations
shows that an (m+n)-fold alpha iterate is the m-fold iterate followed by the
n-fold iterate at its endpoint. Split the r-fold incoming iterate after p steps,
at first index zero. Since r>=p, this is the incoming p-fold iterate followed by
lambda, with the canonical endpoint transports. Precomposition by the source
transport does not change its image. Factor the incoming p-fold iterate through
its image and cancel its epimorphic image projection when computing the image
after lambda. The filtration formula identifies that image with F(p), so the
image of inc r u v is the subobject represented by F(p).arrow followed by lambda.
Both this composite and inc are monomorphic. Subobject.isoOfMkEqMk therefore
gives the isomorphism between their domains, and its defining commutative equation
is exactly the required lift equation. For p=0 the first part of the split is
an identity; nothing in this argument requires q>=a. -/
theorem finitePage_image_lift
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (hinc0 : ∀ p q : ℤ, inc 0 p q = 𝟙 _)
    (hinc : ∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q)
    (p q : ℤ) (hp : 0 ≤ p)
    (F : PBCDecreasingFiltration (X.D 0 (p + q)))
    (hF : ∀ i : ℤ, 0 ≤ i → F.step i =
      imageSubobject (X.incomingAlphaIter i.toNat 0 (p + q)))
    (lambda : X.D 0 (p + q) ⟶
      X.D (p - max (p + 3) (q - a + 2) + 2) (q + max (p + 3) (q - a + 2) - 2))
    (hlambda : lambda = X.alphaIter
      (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
        eqToHom (by congr 1 <;> omega))
    [IsIso lambda] :
    ∃ (lift : (F.step p : B) ⟶
        (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
          (p - max (p + 3) (q - a + 2) + 2)
          (q + max (p + 3) (q - a + 2) - 2)),
      IsIso lift ∧
      lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
          (p - max (p + 3) (q - a + 2) + 2)
          (q + max (p + 3) (q - a + 2) - 2) = (F.step p).arrow ≫ lambda := by
  classical
  let R : ℤ := max (p + 3) (q - a + 2)
  let r : ℕ := R.toNat - 2
  let u : ℤ := p - R + 2
  let v : ℤ := q + R - 2
  have hR : 2 ≤ R := by dsimp [R]; omega
  have hr : (r : ℤ) = R - 2 := by dsimp [r]; omega
  have hrp : p.toNat ≤ r := by dsimp [R] at *; omega
  obtain ⟨hmono, himage⟩ := prescribed_inclusion_images X inc hinc0 hinc
  have := hmono r u v
  have hsplit : X.incomingAlphaIter r u v ≍
      X.incomingAlphaIter p.toNat 0 (p + q) ≫ lambda := by
    have hn : X.incomingAlphaIter r u v ≍
        X.incomingAlphaIter r ((p.toNat : ℤ) - r) (q + r) := by
      dsimp [u, v]
      congr! 1 <;> omega
    apply hn.trans
    apply (incoming_split_heq X r p.toNat q hrp).trans
    rw [hlambda]
    simp only [← Category.assoc, heq_comp_eqToHom_iff]
    apply heq_comp (by congr 1; omega) (by congr 1; omega)
      (by congr 1 <;> (dsimp [u, R] at *; omega))
    · congr! 1; omega
    · congr! 1 <;> (dsimp [u, R] at *; omega)
  have hsplitEq : X.incomingAlphaIter r u v =
      eqToHom (by congr 1 <;> dsimp [u, v] <;> omega) ≫
        (X.incomingAlphaIter p.toNat 0 (p + q) ≫ lambda) := by
    apply eq_of_heq
    exact hsplit.trans (eqToHom_comp_heq _ _).symm
  have him : imageSubobject (inc r u v) =
      Subobject.mk ((F.step p).arrow ≫ lambda) := by
    rw [himage, hsplitEq, imageSubobject_iso_comp]
    have hF0 := hF p hp
    simp only [← imageSubobject_arrow_comp_assoc
      (X.incomingAlphaIter p.toNat 0 (p + q))]
    rw [imageSubobject_comp_of_epi]
    have heq : Subobject.mk ((imageSubobject
        (X.incomingAlphaIter p.toNat 0 (p + q))).arrow ≫ lambda) =
        Subobject.mk ((F.step p).arrow ≫ lambda) := by
      rw [← hF0]
    exact (imageSubobject_mono _).trans heq
  let e : (F.step p : B) ≅ (X.pageCouple r).D u v :=
    Subobject.isoOfMkEqMk ((F.step p).arrow ≫ lambda) (inc r u v)
      ((imageSubobject_mono _).symm.trans him).symm
  have he : e.hom ≫ inc r u v = (F.step p).arrow ≫ lambda := by
    simp [e]
  exact ⟨e.hom, inferInstance, he⟩

end CategoryTheory
