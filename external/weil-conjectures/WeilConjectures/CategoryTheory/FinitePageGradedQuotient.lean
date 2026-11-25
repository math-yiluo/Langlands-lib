/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import all WeilConjectures.CategoryTheory.FinitePageImageLift
import all WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# The graded quotient induced by derived g

Source: blueprint lemma-uniform-bound-proper-direct-image--1, steps 5--6; Stacks Tags 011R, 011S and
0AMJ. (blueprint: lem-sp-finite-page-graded-quotient)
-/

@[expose] public section

universe u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem derivedDInclusion_kernel
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    {s : ℕ} (Y : BigradedExactCouple B s) (p q : ℤ) :
    imageSubobject (Y.derivedDInclusion p q) = kernelSubobject (Y.g p q) := by
  have aux (i j p q : ℤ) (hp : i - 1 = p) (hq : j + 1 = q) :
      imageSubobject (image.ι (Y.alpha i j) ≫
        eqToHom (congrArg₂ Y.D hp hq)) = kernelSubobject (Y.g p q) := by
    subst p
    subst q
    simpa only [eqToHom_refl, Category.comp_id, imageSubobject_mono]
      using Y.exact_g i j
  exact aux (p + 1) (q - 1) p q (by omega) (by omega)

/-- Once the image lift is fixed, derived g induces the finite-page graded isomorphism.
Source: blueprint lemma-uniform-bound-proper-direct-image--1, proof steps 5--6; Stacks Tags 011R,
011S and 0AMJ. (blueprint: lem-sp-finite-page-graded-quotient)

Proof: Write R=max(p+3,q-a+2), r=R-2, u=p-r and v=q+r. The inclusion inc r is
monomorphic and its image is the incoming r-fold alpha image, by induction on its
specified recurrence and pageCouple_image. The next inclusion inc (r+1) factors
as the incoming derived-alpha image inclusion followed by inc r. Splitting the
incoming (r+1)-fold alpha iterate at first index zero identifies its image with
the image of F(p+1).arrow followed by lambda. Since lift followed by inc r is
F(p).arrow followed by lambda and both inc r and lambda are monomorphic, this
identifies the inclusion F(p+1) into F(p), under lift, with the incoming derived
alpha image. Exactness of the r-th couple identifies that image with ker(g).
The target of derived f after g is zero: derived D(p+2,q-1) embeds into D(p+2,q-1)
as the incoming r-fold image with source D(p+R,q-R+1). This source is zero since
R>=q-a+2. Thus f=0 and exactness at derived E makes g epimorphic. Composing
with lift and the index transport preserves epimorphicity and the indicated
kernel. The abelian cokernel property gives the unique isomorphism from
F(p)/F(p+1) to page R(p,q) whose composite with the projection is lift followed
by g and index transport. At p=0 the argument uses the identity incoming iterate;
when q<a its epimorphic quotient has zero target, with the same universal property.
No choice of an arbitrary isomorphism is used: its hom is fixed by the epimorphic
cokernel projection and the displayed equation. -/
theorem finitePage_graded_quotient
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
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
    [IsIso lambda]
    (lift : (F.step p : B) ⟶
        (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
          (p - max (p + 3) (q - a + 2) + 2)
          (q + max (p + 3) (q - a + 2) - 2))
    (hlift : IsIso lift)
    (hliftinc : lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
      (p - max (p + 3) (q - a + 2) + 2)
      (q + max (p + 3) (q - a + 2) - 2) = (F.step p).arrow ≫ lambda) :
    ∃ (psi : F.gradedPiece p ≅ X.page (max (p + 3) (q - a + 2)).toNat p q),
      cokernel.π (Subobject.ofLE (F.step (p + 1)) (F.step p)
          (F.antitone_step (by omega))) ≫ psi.hom = lift ≫
        (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).g
          (p - max (p + 3) (q - a + 2) + 2)
          (q + max (p + 3) (q - a + 2) - 2) ≫
        eqToHom (by unfold BigradedExactCouple.page; congr 1 <;> omega) := by
  classical
  let R : ℤ := max (p + 3) (q - a + 2)
  let r : ℕ := R.toNat - 2
  let u : ℤ := p - R + 2
  let v : ℤ := q + R - 2
  let Y := X.pageCouple r
  let k := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  let t : Y.E (u + r) (v - r) ⟶ X.page R.toNat p q :=
    eqToHom (by dsimp [Y, BigradedExactCouple.page, u, v, r, R]; congr 1 <;> omega)
  let π := lift ≫ Y.g u v ≫ t
  have hR : 2 ≤ R := by dsimp [R]; omega
  have hr : (r : ℤ) = R - 2 := by dsimp [r]; omega
  have hrp : (p + 1).toNat ≤ r + 1 := by dsimp [R] at *; omega
  obtain ⟨hmono, himage⟩ := prescribed_inclusion_images X inc hinc0 hinc
  have : Mono (inc r u v) := hmono r u v
  have : Mono (inc (r + 1) u v) := hmono (r + 1) u v
  have hsplit : X.incomingAlphaIter (r + 1) u v ≍
      X.incomingAlphaIter (p + 1).toNat 0 (p + q) ≫ lambda := by
    have hn : X.incomingAlphaIter (r + 1) u v ≍
        X.incomingAlphaIter (r + 1) (((p + 1).toNat : ℤ) - (r + 1))
          ((q - 1) + (r + 1)) := by
      dsimp [u, v]
      congr! 1 <;> omega
    apply hn.trans
    apply (incoming_split_heq X (r + 1) (p + 1).toNat (q - 1) hrp).trans
    rw [hlambda]
    simp only [← Category.assoc, heq_comp_eqToHom_iff]
    apply heq_comp (by congr 1; omega) (by congr 1; omega)
      (by congr 1 <;> (dsimp [u, R] at *; omega))
    · congr! 1; omega
    · congr! 1 <;> (dsimp [u, R] at *; omega)
  have hsplitEq : X.incomingAlphaIter (r + 1) u v =
      eqToHom (by congr 1 <;> dsimp [u, v] <;> omega) ≫
        (X.incomingAlphaIter (p + 1).toNat 0 (p + q) ≫ lambda) := by
    apply eq_of_heq
    exact hsplit.trans (eqToHom_comp_heq _ _).symm
  have him : imageSubobject (inc (r + 1) u v) =
      Subobject.mk ((F.step (p + 1)).arrow ≫ lambda) := by
    rw [himage, hsplitEq, imageSubobject_iso_comp]
    simp only [← imageSubobject_arrow_comp_assoc
      (X.incomingAlphaIter (p + 1).toNat 0 (p + q))]
    rw [imageSubobject_comp_of_epi, imageSubobject_mono, ← hF (p + 1) (by omega)]
  have hl : IsIso lift := hlift
  have hkinc : (k ≫ lift) ≫ inc r u v = (F.step (p + 1)).arrow ≫ lambda := by
    rw [Category.assoc, hliftinc, ← Category.assoc]
    dsimp [k]
    rw [Subobject.ofLE_arrow]
  have hd : Mono (Y.derivedDInclusion u v) := by
    dsimp [BigradedExactCouple.derivedDInclusion]
    infer_instance
  have hk : Subobject.mk (k ≫ lift) = kernelSubobject (Y.g u v) := by
    apply Subobject.map_obj_injective (inc r u v)
    rw [← derivedDInclusion_kernel Y u v, imageSubobject_mono]
    simp only [Subobject.map_mk, hkinc]
    rw [← him]
    change imageSubobject (inc (r + 1) u v) =
      Subobject.mk ((X.pageCouple r).derivedDInclusion u v ≫ inc r u v)
    simp only [← hinc, imageSubobject_mono]
  have hnext : IsZero (Y.D ((u + r) + 2) ((v - r) - 1)) :=
    BigradedExactCouple.pageD_zero X a hDzero r _ _ (by dsimp [u, v, R] at *; omega)
  have hf : Y.f (u + r) (v - r) = 0 := hnext.eq_zero_of_tgt _
  have hepi : Epi (Y.g u v) := by
    have himg : imageSubobject (Y.g u v) = ⊤ := by
      rw [Y.exact_f, hf, kernelSubobject_zero]
    have : IsIso (imageSubobject (Y.g u v)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).mpr himg
    rw [← imageSubobject_arrow_comp (Y.g u v)]
    infer_instance
  have : Epi π := by dsimp [π]; infer_instance
  have hker : kernelSubobject π = Subobject.mk k := by
    have hπ : π = (lift ≫ Y.g u v) ≫ t := by simp only [π, Category.assoc]
    simp only [hπ, kernelSubobject_comp_mono]
    apply Subobject.map_obj_injective lift
    have hmap : (Subobject.map lift).obj (kernelSubobject (lift ≫ Y.g u v)) =
        kernelSubobject (Y.g u v) := by
      conv_lhs => rw [← Subobject.mk_arrow (kernelSubobject (lift ≫ Y.g u v))]
      rw [Subobject.map_mk, ← Subobject.mk_arrow (kernelSubobject (Y.g u v))]
      exact Subobject.mk_eq_mk_of_comm _ _ (kernelSubobjectIsoComp lift (Y.g u v))
        (kernelSubobjectIsoComp_hom_arrow lift (Y.g u v))
    rw [hmap, Subobject.map_mk]
    exact hk.symm
  obtain ⟨e, he⟩ := BigradedExactCouple.quotient_comparison (F.step (p + 1)) (F.step p)
    (F.antitone_step (by omega)) π hker
  exact ⟨e, he⟩

end CategoryTheory
