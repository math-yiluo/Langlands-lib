/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import WeilConjectures.RingTheory.Rescaling.PolynomialRescaling

/-! # Realization of polynomial rescaling on relative affine space -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MvPolynomial
namespace AlgebraicGeometry.AffineSpace

variable (σ : Type u) (S : Scheme.{u})

private def ceval : MvPolynomial σ Γ(S, ⊤) →+* Γ(AffineSpace σ S, ⊤) :=
  eval₂Hom (AffineSpace σ S ↘ S).appTop.hom (coord S)

private lemma ceval_bijective [IsAffine S] : Function.Bijective (ceval σ S) := by
  have h : CommRingCat.ofHom (ceval σ S) =
      (Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine σ S).hom.appTop := by
    rw [isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
    rfl
  rw [show ceval σ S = (CommRingCat.ofHom (ceval σ S)).hom from rfl, h]
  exact ConcreteCategory.bijective_of_isIso _

private def coordEquiv [IsAffine S] :
    MvPolynomial σ Γ(S, ⊤) ≃+* Γ(AffineSpace σ S, ⊤) :=
  RingEquiv.ofBijective (ceval σ S) (ceval_bijective σ S)

private lemma coordEquiv_C [IsAffine S] (r : Γ(S, ⊤)) :
    coordEquiv σ S (C r) = (AffineSpace σ S ↘ S).appTop r := by
  exact eval₂Hom_C _ _ _

private lemma coordEquiv_X [IsAffine S] (i : σ) :
    coordEquiv σ S (X i) = coord S i := by
  exact eval₂Hom_X' _ _ _

private def ringAction (e : AffineSpace σ S ≅ AffineSpace σ S) :
    Γ(AffineSpace σ S, ⊤) ≃+* Γ(AffineSpace σ S, ⊤) :=
  { e.hom.appTop.hom with
    invFun := e.inv.appTop
    left_inv := by
      intro r
      change e.inv.appTop (e.hom.appTop r) = r
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
      rfl
    right_inv := by
      intro r
      change e.hom.appTop (e.inv.appTop r) = r
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
      rfl }

private def polynomialAction [IsAffine S] (e : AffineSpace σ S ≅ AffineSpace σ S)
    (he : e.hom ≫ AffineSpace σ S ↘ S = AffineSpace σ S ↘ S) :
    MvPolynomial σ Γ(S, ⊤) ≃ₐ[Γ(S, ⊤)] MvPolynomial σ Γ(S, ⊤) :=
  AlgEquiv.ofRingEquiv (f := (coordEquiv σ S).trans
    ((ringAction σ S e).trans (coordEquiv σ S).symm)) (by
      intro r
      apply (coordEquiv σ S).injective
      change coordEquiv σ S ((coordEquiv σ S).symm
        (e.hom.appTop (coordEquiv σ S (C r)))) = coordEquiv σ S (C r)
      rw [RingEquiv.apply_symm_apply, coordEquiv_C,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he])

private lemma polynomialAction_coord [IsAffine S] (e : AffineSpace σ S ≅ AffineSpace σ S)
    (he : e.hom ≫ AffineSpace σ S ↘ S = AffineSpace σ S ↘ S) (i : σ) :
    ceval σ S (polynomialAction σ S e he (X i)) = e.hom.appTop (coord S i) := by
  change coordEquiv σ S ((coordEquiv σ S).symm
    (e.hom.appTop (coordEquiv σ S (X i)))) = _
  rw [RingEquiv.apply_symm_apply, coordEquiv_X]

private abbrev Line := AffineSpace PUnit.{u + 1} S
private abbrev Total := AffineSpace σ (Line S)
private abbrev Poly := Polynomial (MvPolynomial σ Γ(S, ⊤))

private def peval : Poly σ S →+* Γ(Total σ S, ⊤) :=
  Polynomial.eval₂RingHom
    (eval₂Hom ((Total σ S ↘ Line S) ≫ (Line S ↘ S)).appTop.hom (coord (Line S)))
    ((Total σ S ↘ Line S).appTop (coord S PUnit.unit))

private lemma peval_C_X (i : σ) : peval σ S (Polynomial.C (X i)) = coord (Line S) i := by
  simp [peval]

private lemma peval_C_C (r : Γ(S, ⊤)) :
    peval σ S (Polynomial.C (C r)) = ((Total σ S ↘ Line S) ≫ (Line S ↘ S)).appTop r := by
  simp [peval]

private lemma peval_X : peval σ S Polynomial.X =
    (Total σ S ↘ Line S).appTop (coord S PUnit.unit) := by
  simp [peval]

private def realize (E : Poly σ S ≃+* Poly σ S) : Total σ S ⟶ Total σ S :=
  homOfVector (Total σ S ↘ Line S) (fun i ↦ peval σ S (E (Polynomial.C (X i))))

private lemma realize_over (E : Poly σ S ≃+* Poly σ S) :
    realize σ S E ≫ Total σ S ↘ Line S = Total σ S ↘ Line S :=
  homOfVector_over _ _

private lemma realize_peval (E : Poly σ S ≃+* Poly σ S)
    (hX : E Polynomial.X = Polynomial.X)
    (hC : ∀ r : Γ(S, ⊤), E (Polynomial.C (C r)) = Polynomial.C (C r))
    (p : Poly σ S) :
    (realize σ S E).appTop (peval σ S p) = peval σ S (E p) := by
  have h : (realize σ S E).appTop.hom.comp (peval σ S) =
      (peval σ S).comp E.toRingHom := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        change (realize σ S E).appTop (peval σ S (Polynomial.C (C r))) =
          peval σ S (E (Polynomial.C (C r)))
        rw [hC, peval_C_C]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc,
          realize_over]
      · intro i
        change (realize σ S E).appTop (peval σ S (Polynomial.C (X i))) =
          peval σ S (E (Polynomial.C (X i)))
        rw [peval_C_X, realize, homOfVector_appTop_coord]
    · change (realize σ S E).appTop (peval σ S Polynomial.X) = peval σ S (E Polynomial.X)
      rw [hX, peval_X]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, realize_over]
  exact DFunLike.congr_fun h p

private def realizeIso (E : Poly σ S ≃+* Poly σ S)
    (hX : E Polynomial.X = Polynomial.X)
    (hC : ∀ r : Γ(S, ⊤), E (Polynomial.C (C r)) = Polynomial.C (C r)) :
    Total σ S ≅ Total σ S where
  hom := realize σ S E
  inv := realize σ S E.symm
  hom_inv_id := by
    apply hom_ext
    · simp [Category.assoc, realize_over]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, realize,
        homOfVector_appTop_coord]
      rw [← realize, realize_peval σ S E hX hC, E.apply_symm_apply, peval_C_X]
      rfl
  inv_hom_id := by
    have hX' : E.symm Polynomial.X = Polynomial.X := by
      apply E.injective
      rw [E.apply_symm_apply, hX]
    have hC' (r : Γ(S, ⊤)) : E.symm (Polynomial.C (C r)) = Polynomial.C (C r) := by
      apply E.injective
      rw [E.apply_symm_apply, hC]
    apply hom_ext
    · simp [Category.assoc, realize_over]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, realize,
        homOfVector_appTop_coord]
      rw [← realize, realize_peval σ S E.symm hX' hC', E.symm_apply_apply, peval_C_X]
      rfl

private def sectionAt (a : Γ(S, ⊤)) : S ⟶ Line S := homOfVector (𝟙 S) (fun _ ↦ a)

private lemma peval_endpoint (a : Γ(S, ⊤)) (p : Poly σ S) :
    (map σ (sectionAt S a)).appTop (peval σ S p) =
      ceval σ S (p.eval (C a)) := by
  have h : (map σ (sectionAt S a)).appTop.hom.comp (peval σ S) =
      (ceval σ S).comp (Polynomial.evalRingHom (C a)) := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.coe_comp, Function.comp_apply, peval_C_C,
          Polynomial.coe_evalRingHom, Polynomial.eval_C, ceval, eval₂Hom_C]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_over_assoc]
        simp [sectionAt]
      · intro i
        simp [peval_C_X, ceval]
    · simp only [RingHom.coe_comp, Function.comp_apply, peval_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_X]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_over,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp [sectionAt, ceval]
  exact DFunLike.congr_fun h p

/-- A polynomial rescaling family realized by the universal property of relative
 affine space. Source: Furter--Poloni, Lemma 3.1, pp. 5--6, with the coordinate
 realization written by J1. Proof: identify global sections with the polynomial
 ring using the affine-space spectrum isomorphism. Apply polynomial rescaling.
 Evaluate its coordinate polynomials on the total space; the inverse coordinate
 polynomials give the inverse morphism. Polynomial extensionality shows that
 substitution commutes with evaluation and with the two parameter sections.
 (blueprint: lem-pur-polynomial-family-realization). -/
theorem polynomial_deformation [IsAffine S] [Fintype σ] [DecidableEq σ]
    (e : AffineSpace σ S ≅ AffineSpace σ S)
    (he : e.hom ≫ AffineSpace σ S ↘ S = AffineSpace σ S ↘ S) :
    ∃ (g : Matrix.GeneralLinearGroup σ Γ(S, ⊤))
      (E : AffineSpace σ (AffineSpace PUnit.{u + 1} S) ≅
        AffineSpace σ (AffineSpace PUnit.{u + 1} S)),
      E.hom ≫ AffineSpace σ (AffineSpace PUnit.{u + 1} S) ↘
        AffineSpace PUnit.{u + 1} S =
          AffineSpace σ (AffineSpace PUnit.{u + 1} S) ↘ AffineSpace PUnit.{u + 1} S ∧
      map σ (zeroSection PUnit.{u + 1} S) ≫ E.hom =
        homOfVector (AffineSpace σ S ↘ S)
          (fun i ↦ ∑ j : σ, (AffineSpace σ S ↘ S).appTop (g i j) * coord S j) ≫
            map σ (zeroSection PUnit.{u + 1} S) ∧
      map σ (oneSection PUnit.{u + 1} S) ≫ E.hom =
        e.hom ≫ map σ (oneSection PUnit.{u + 1} S) := by
  obtain ⟨g, E, hX, hC, h1, h0⟩ :=
    MvPolynomial.Rescaling.exists_deformation (polynomialAction σ S e he)
  refine ⟨g, realizeIso σ S E hX hC, realize_over σ S E, ?_, ?_⟩
  · apply hom_ext
    · simp [Category.assoc, realizeIso, realize_over]
    · intro i
      change (map σ (sectionAt S 0) ≫ realize σ S E).appTop (coord (Line S) i) = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, realize,
        homOfVector_appTop_coord, peval_endpoint]
      simp only [map_zero, h0, ceval, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        map_appTop_coord, homOfVector_appTop_coord]
  · apply hom_ext
    · simp [Category.assoc, realizeIso, realize_over, he]
    · intro i
      change (map σ (sectionAt S 1) ≫ realize σ S E).appTop (coord (Line S) i) = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, realize,
        homOfVector_appTop_coord, peval_endpoint]
      simp only [map_one, h1, polynomialAction_coord]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_appTop_coord]

end AlgebraicGeometry.AffineSpace
