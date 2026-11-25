/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits

/-!
# Finite exact-couple quotient kernels

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R, 011T and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem quotient_kernel {T U : C} (S R : Subobject U) (hSR : S ≤ R)
    (e : T ⟶ (R : C)) :
    kernelSubobject (e ≫ cokernel.π (Subobject.ofLE S R hSR)) =
      (Subobject.pullback (e ≫ R.arrow)).obj S := by
  let k := Subobject.ofLE S R hSR
  have htest {V : C} (a : V ⟶ T) :
      (kernelSubobject (e ≫ cokernel.π k)).Factors a ↔
        S.Factors (a ≫ e ≫ R.arrow) := by
    rw [kernelSubobject_factors_iff]
    constructor
    · intro hz
      let l := Abelian.monoLift k (a ≫ e) (by simpa only [Category.assoc] using hz)
      apply (Subobject.factors_iff _ _).mpr
      refine ⟨l, ?_⟩
      calc
        l ≫ S.arrow = l ≫ k ≫ R.arrow := by simp [k]
        _ = a ≫ e ≫ R.arrow := by simp [l]
    · intro hfac
      let l := S.factorThru _ hfac
      have hl := S.factorThru_arrow _ hfac
      have he : l ≫ k = a ≫ e := by
        apply (cancel_mono R.arrow).mp
        simpa only [Category.assoc, Subobject.ofLE_arrow, k] using hl
      rw [← Category.assoc, ← he, Category.assoc, cokernel.condition, comp_zero]
  apply le_antisymm
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (pullback_factors_iff _ _ _).mpr
    apply (htest _).mp
    exact kernelSubobject_factors _ _ (kernelSubobject_arrow_comp _)
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (htest _).mpr
    apply (pullback_factors_iff _ _ _).mp
    exact (Subobject.factors_iff _ _).mpr ⟨𝟙 _, by simp⟩

private theorem cocone_iso_nonpositive (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (n : ℤ) (A : AlphaColimit X n)
    (hA : A.obj = X.D 0 n)
    (hι : A.ι 0 ≫ eqToHom hA = eqToHom (by congr 1; omega))
    (p : ℤ) (hp : p ≤ 0) : IsIso (A.ι p) := by
  have hzero : IsIso (A.ι 0) := by
    have : IsIso (A.ι 0 ≫ eqToHom hA) := by
      rw [hι]
      infer_instance
    exact IsIso.of_isIso_comp_right (A.ι 0) (eqToHom hA)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    let t := X.alphaDiagonal n (-((k + 1 : ℕ) : ℤ))
    have : IsIso t := by
      dsimp [t, alphaDiagonal]
      have := alpha_iso_left X hE (-((k : ℤ) + 1) + 1)
        (n - (-((k : ℤ) + 1) + 1)) (by omega)
      infer_instance
    have : IsIso (t ≫ A.ι (-((k + 1 : ℕ) : ℤ))) := by
      dsimp [t]
      rw [A.comm]
      have he : -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) := by omega
      exact Eq.mp (congrArg (fun i : ℤ ↦ IsIso (A.ι i)) he.symm) (ih (by omega))
    exact IsIso.of_isIso_comp_left t _

private theorem alphaIter_cocone (X : BigradedExactCouple C 0)
    (n : ℤ) (A : AlphaColimit X n) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
    X.alphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ A.ι (p - r) =
      eqToHom (by congr 1; omega) ≫ A.ι p := by
  induction r generalizing p q with
  | zero =>
    apply eq_of_heq
    simp only [alphaIter, eqToHom_trans_assoc,
      eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    congr! 1
    omega
  | succ r ih =>
    have htail : X.alphaIter r (p - 1) (q + 1) ≫
        eqToHom (by congr 1 <;> omega) ≫ A.ι (p - (r + 1 : ℕ)) =
        eqToHom (by congr 1; omega) ≫ A.ι (p - 1) := by
      have hh := ih (p - 1) (q + 1) (by omega)
      apply eq_of_heq
      have hleft : X.alphaIter r (p - 1) (q + 1) ≫
          eqToHom (by congr 1 <;> omega) ≫ A.ι (p - (r + 1 : ℕ)) ≍
          X.alphaIter r (p - 1) (q + 1) ≫
            eqToHom (by congr 1; omega) ≫ A.ι (p - 1 - r) := by
        apply heq_comp rfl rfl rfl HEq.rfl
        simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
        congr! 1
        omega
      exact hleft.trans (heq_of_eq hh)
    simp only [alphaIter, Category.assoc, eqToHom_trans_assoc]
    rw [htail]
    apply eq_of_heq
    have hm : X.alpha p q ≫ eqToHom (by congr 1; omega) ≫ A.ι (p - 1) ≍
        X.alphaDiagonal n (p - 1) ≫ A.ι (p - 1) := by
      dsimp [alphaDiagonal]
      simp only [Category.assoc]
      apply heq_comp (f := X.alpha p q)
        (f' := X.alpha (p - 1 + 1) (n - (p - 1 + 1)))
        (by congr 1 <;> omega) (by congr 1 <;> omega) rfl
      · congr! 1 <;> omega
      · simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
        rfl
    apply (hm.trans (heq_of_eq (A.comm (p - 1)))).trans
    rw [heq_eqToHom_comp_iff]
    congr! 1
    omega

private theorem incomingAlphaIter_cocone (X : BigradedExactCouple C 0)
    (n : ℤ) (A : AlphaColimit X n) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
    X.incomingAlphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ A.ι p =
      eqToHom (by congr 1; omega) ≫ A.ι (p + r) := by
  have hh := alphaIter_cocone X n A r (p + r) (q - r) (by omega)
  apply eq_of_heq
  have hleft : X.incomingAlphaIter r p q ≫
      eqToHom (by congr 1; omega) ≫ A.ι p ≍
      X.alphaIter r (p + r) (q - r) ≫
        eqToHom (by congr 1; omega) ≫ A.ι (p + r - r) := by
    simp only [incomingAlphaIter, Category.assoc, eqToHom_trans_assoc]
    apply heq_comp rfl rfl rfl HEq.rfl
    simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    congr! 1
    omega
  exact hleft.trans (heq_of_eq hh)

/-- In the normalized left half-plane, the graded quotient has the finite alpha kernel.

Proof: Exactness and vanishing of the two adjacent initial E terms show that
alpha is invertible at nonpositive first index. The normalized zeroth cocone map
is invertible, so iteration of the cocone equation shows the cocone map at
u=p-r is invertible when p<=r. The cocone equations identify iota_p with
alphaIter r followed by this invertible cocone map, with the source transport.
They identify iota_(p+1) with incomingAlphaIter (r+1) at (u,q+r) followed
by the same map. Thus the next filtration image is that incoming image transported
through an isomorphism. The kernel of the graded-piece projection is the next
filtration step inside the current step: a monomorphism is the kernel of its
cokernel in an abelian category. Pulling this kernel back along the image
projection of iota_p gives the inverse image of the next filtration step along
iota_p. Cancel the invertible cocone map in this pullback, obtaining the formula.
This also covers r=0 and negative p: the transported identities and zero graded
pieces obey the same kernel calculation.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, finite images
in the normalized alpha colimit; Stacks Tags 011T and 0AMJ.
(blueprint: lem-sp-normalized-graded-finite-kernel) -/
theorem normalizedGraded_finite_kernel (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n : ℤ, (A n).obj = X.D 0 n)
    (hι : ∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
      eqToHom (by congr 1; omega))
    (r : ℕ) (p q : ℤ) (hp : p ≤ (r : ℤ)) :
    kernelSubobject (X.toGradedPiece A p q) =
      (Subobject.pullback (X.alphaIter r p q)).obj
        (imageSubobject (X.incomingAlphaIter (r + 1) (p - r) (q + r))) := by
  let n := p + q
  let u := p - (r : ℤ)
  let v := q + (r : ℤ)
  let a := X.alphaIter r p q
  let b := X.incomingAlphaIter (r + 1) u v
  let c : X.D u v ⟶ (A n).obj :=
    eqToHom (by congr 1; dsimp [n, u, v]; omega) ≫ (A n).ι u
  have : IsIso ((A n).ι u) :=
    cocone_iso_nonpositive X hE n (A n) (hA n) (hι n) u (by dsimp [u]; omega)
  have : IsIso c := by dsimp [c]; infer_instance
  have hac : a ≫ c = eqToHom (by congr 1; dsimp [n]; omega) ≫ (A n).ι p := by
    exact alphaIter_cocone X n (A n) r p q rfl
  have hbc : b ≫ c = eqToHom (by congr 1 <;> dsimp [n, u, v] <;> omega) ≫
      (A n).ι (p + 1) := by
    have hh := incomingAlphaIter_cocone X n (A n) (r + 1) u v
      (by dsimp [n, u, v]; omega)
    apply eq_of_heq
    apply (heq_of_eq hh).trans
    simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    congr! 1
    dsimp [u]
    omega
  let F := X.imageFiltration n (A n)
  let e : X.D p q ⟶ (F.step p : C) :=
    eqToHom (by congr 1; dsimp [n]; omega) ≫ factorThruImageSubobject ((A n).ι p)
  have he : e ≫ (F.step p).arrow = a ≫ c := by
    dsimp [e, F, imageFiltration]
    simp only [Category.assoc, imageSubobject_arrow_comp]
    exact hac.symm
  have hk : kernelSubobject (X.toGradedPiece A p q) =
      (Subobject.pullback (a ≫ c)).obj (F.step (p + 1)) := by
    have hg : X.toGradedPiece A p q = e ≫ cokernel.π
        (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))) := by
      dsimp [toGradedPiece, e, F, n]
      rw [Category.assoc]
    rw [hg, quotient_kernel, he]
  have him : F.step (p + 1) = (Subobject.map c).obj (imageSubobject b) := by
    change imageSubobject ((A n).ι (p + 1)) = _
    have hbi : imageSubobject (b ≫ c) = imageSubobject ((A n).ι (p + 1)) := by
      simp only [hbc, imageSubobject_iso_comp]
    rw [← hbi, Subobject.map_obj_eq_mk]
    have : StrongEpi (factorThruImageSubobject b) := strongEpi_of_epi _
    simpa only [imageSubobject_arrow_comp_assoc] using
      Subobject.imageSubobject_eq_mk (factorThruImageSubobject b)
        ((imageSubobject b).arrow ≫ c)
  rw [hk, him, Subobject.pullback_comp, Subobject.pullback_map_self]

end CategoryTheory.BigradedExactCouple
