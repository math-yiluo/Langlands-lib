/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces

import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Local spanning of associated graded quotients

Source: Stacks Project, proof of Lemma 0884, affine power refinement.
(blueprint: lem-weil-pbc-formal-polynomial-quotient-span).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem evaluation_mem_span
    {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R)
    {r : ℕ} (generators : Fin r → A) (k : ℕ) (v : R)
    (hv : v ∈ Ideal.span (Set.range (fun i => ρ (generators i))) ^ k) :
    v ∈ Submodule.span R (Set.range (fun b :
      MvPolynomial.homogeneousSubmodule (Fin r) A k =>
        MvPolynomial.eval₂Hom ρ (fun i => ρ (generators i)) b.val)) := by
  classical
  obtain ⟨p, hp, he⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous _ _).mp hv
  rw [← he, MvPolynomial.as_sum p, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hdegree : d.degree = k := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero hn)
  let b : MvPolynomial.homogeneousSubmodule (Fin r) A k :=
    ⟨MvPolynomial.monomial d 1, MvPolynomial.isHomogeneous_monomial 1 hdegree⟩
  have hb : MvPolynomial.eval₂Hom ρ (fun i => ρ (generators i)) b.val ∈
      Submodule.span R (Set.range (fun b :
        MvPolynomial.homogeneousSubmodule (Fin r) A k =>
          MvPolynomial.eval₂Hom ρ (fun i => ρ (generators i)) b.val)) :=
    Submodule.subset_span ⟨b, rfl⟩
  have heq : MvPolynomial.eval (fun i => ρ (generators i))
      (MvPolynomial.monomial d (AddMonoidAlgebra.coeff p d)) =
        AddMonoidAlgebra.coeff p d •
          MvPolynomial.eval₂Hom ρ (fun i => ρ (generators i)) b.val := by
    simp [b, MvPolynomial.eval_monomial, MvPolynomial.eval₂_monomial, smul_eq_mul]
  rw [heq]
  exact Submodule.smul_mem _ _ hb

set_option backward.isDefEq.respectTransparency false in
/-- Projections of homogeneous evaluation lifts locally span each graded quotient.
Source: Stacks Project, proof of Lemma 0884, associated graded algebra refinement;
Schemes, Tags 01I8 and 01IC, for affine quotients and ideal powers.
(blueprint: lem-weil-pbc-formal-polynomial-quotient-span).

Proof: fix k, U and a point y of U. Choose an affine neighbourhood W contained in U.
Every power module is quasi-coherent: in degree zero it is the structure module,
and in positive degrees use ideal_times_quasiCoherent_affine_sections. Its affine
quotient-surjectivity clause lifts each restricted section to J^k(W). The images
of these lifts lie in J(W)^k (the inclusion is the identity for k=0). The affine
ideal extension formula identifies J(W) with the span of the images of the given
generators. By Ideal.span_pow_eq_map_homogeneousSubmodule, each image is the
evaluation of a degree-k polynomial over the section ring. Expand that polynomial
as a finite sum of coefficient multiples of monomials of degree k. Each monomial
with coefficient one is defined over A; the stipulated image formula for l says
its evaluation is the image of the corresponding l(k,W,b). Injectivity of the
power inclusion therefore writes the lifted section as a linear combination of
those lifts. Apply the linear quotient projection to get the required span.
The same W works for the whole finite family, since the affine projection is
surjective on every section. In degree zero the constant monomial generates;
with no generators every positive power is zero. An empty family imposes no
condition beyond the affine neighbourhood. -/
theorem formalPolynomial_quotient_span
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {r : ℕ} (generators : Fin r → A)
    (hgenerators : Ideal.span (Set.range generators) = I)
    (l : ∀ (k : ℕ) (U : X.Opens),
      MvPolynomial.homogeneousSubmodule (Fin r) A k →
        (Scheme.idealSheafPower ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).toModulesι k).1.val.obj
          (op U))
    (hl : ∀ k U b, (Scheme.idealSheafPower _ k).2.val.app (op U) (l k U b) =
        MvPolynomial.eval₂Hom
          (((X.presheaf.map (homOfLE (le_top (a := U))).op).hom).comp
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom))
          (fun i => (X.presheaf.map (homOfLE (le_top (a := U))).op).hom
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom (generators i))) b.val) :
    ∀ (k : ℕ) (U : X.Opens) (s : ℕ)
      (a : Fin s → (formalAssociatedGradedPiece ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) k).val.obj (op U))
      (y : X), y ∈ U → ∃ (W : X.Opens) (hWU : W ≤ U), y ∈ W ∧
        ∀ i, (formalAssociatedGradedPiece _ k).val.map (homOfLE hWU).op (a i) ∈
          Submodule.span Γ(X, W)
            (Set.range (fun b => (formalAssociatedGradedπ _ k).val.app (op W) (l k W b)))
      := by
  classical
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let ρ (U : X.Opens) : A →+* Γ(X, U) :=
    ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom).comp
      (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)
  let ev (U : X.Opens) : MvPolynomial (Fin r) A →+* Γ(X, U) :=
    MvPolynomial.eval₂Hom (ρ U) (fun i => ρ U (generators i))
  change ∀ k U b, (Scheme.idealSheafPower J.toModulesι k).2.val.app (op U)
    (l k U b) = ev U b.val at hl
  intro k U s a y hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  let V : X.affineOpens := ⟨W, hW⟩
  let M := (Scheme.idealSheafPower J.toModulesι k).1
  let inc : M.val.obj (op W) →ₗ[Γ(X, W)] Γ(X, W) :=
    ((Scheme.idealSheafPower J.toModulesι k).2.val.app (op W)).hom
  let π : M.val.obj (op W) →ₗ[Γ(X, W)]
      (formalAssociatedGradedPiece J k).val.obj (op W) :=
    ((formalAssociatedGradedπ J k).val.app (op W)).hom
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have hqc : M.IsQuasicoherent := by
    by_cases hk : k = 0
    · subst k
      exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    · exact (Scheme.Modules.ideal_times_quasiCoherent_affine_sections
        J (SheafOfModules.unit X.ringCatSheaf)).2.2.1 k (Nat.pos_of_ne_zero hk)
  have haff := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J M).2.2.2.1 V
  have hsurj : Function.Surjective π := haff.2.1
  refine ⟨W, hWU, hyW, ?_⟩
  intro i
  obtain ⟨t, ht⟩ := hsurj
    ((formalAssociatedGradedPiece J k).val.map (homOfLE hWU).op (a i))
  have himage : inc t ∈ J.ideal V ^ k := by
    by_cases hk : k = 0
    · subst k
      simp
    · have h := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections
        J (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 V
      have hm : inc t ∈ Set.range ((Scheme.idealSheafPower J.toModulesι k).2.app W) :=
        ⟨t, rfl⟩
      rw [h.2.2.2 k (Nat.pos_of_ne_zero hk)] at hm
      exact hm
  rw [formalPolynomial_extendedIdeal_affine I f generators hgenerators V] at himage
  have hevspan := evaluation_mem_span (ρ W) generators k (inc t) himage
  let S : Submodule Γ(X, W) (M.val.obj (op W)) :=
    Submodule.span Γ(X, W) (Set.range (l k W))
  have hmap : Submodule.map inc S =
      Submodule.span Γ(X, W) (Set.range (fun b :
        MvPolynomial.homogeneousSubmodule (Fin r) A k => ev W b.val)) := by
    dsimp only [S]
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext b
    exact hl k W b
  have hmem : inc t ∈ Submodule.map inc S := hmap.symm ▸ hevspan
  obtain ⟨z, hz, hez⟩ := hmem
  have hzt : z = t := formalPolynomial_power_injective J.toModulesι k W hez
  have hspan : t ∈ S := hzt ▸ hz
  have hquot := Submodule.mem_map_of_mem (f := π) hspan
  dsimp only [S] at hquot
  rw [Submodule.map_span, ← Set.range_comp] at hquot
  exact ht ▸ hquot

end AlgebraicGeometry
