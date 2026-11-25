/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Descending a polynomial hypersurface from the generic residue field

Source: Stacks Project, Tag 0559, first proof, clearing coefficient denominators.
(blueprint: lem-sbc-generic-polynomial-hypersurface-descent)
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open Algebra.TensorProduct
open scoped TensorProduct BigOperators
namespace AlgebraicGeometry

-- At a generic point the residue map identifies the stalk fraction field with the residue field.
private theorem fraction_at_generic {S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (η : S) (hη : IsGenericPoint η Set.univ) :
    let := (S.Γevaluation η).hom.toAlgebra
    IsFractionRing Γ(S, ⊤) (S.residueField η) := by
  have heq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  let := (S.Γevaluation (genericPoint S)).hom.toAlgebra
  have : Nonempty (⊤ : S.Opens) := ⟨⟨genericPoint S, trivial⟩⟩
  have hfrac : IsFractionRing Γ(S, ⊤) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
  let er : S.functionField ≃+* S.residueField (genericPoint S) :=
    RingEquiv.ofBijective (S.residue (genericPoint S)).hom
      ⟨RingHom.injective _, S.residue_surjective (genericPoint S)⟩
  let ea : S.functionField ≃ₐ[Γ(S, ⊤)] S.residueField (genericPoint S) :=
    { er with commutes' a := rfl }
  exact IsFractionRing.of_algEquiv ea


-- Clear the finitely many coefficients, then sum the resulting monomials over the same support.
private theorem clear_polynomial
    {A K : Type u} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    {σ : Type v} (Q : MvPolynomial σ K) :
    ∃ (P : MvPolynomial σ A) (d : nonZeroDivisors A),
      MvPolynomial.map (algebraMap A K) P = (d : A) • Q := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors A) Q.support (fun i ↦ AddMonoidAlgebra.coeff Q i)
  change ∀ i ∈ Q.support, ∃ a : A, algebraMap A K a =
    (d : A) • AddMonoidAlgebra.coeff Q i at hd
  let P : MvPolynomial σ A :=
    ∑ i : Q.support, MvPolynomial.monomial i.val (hd i.val i.prop).choose
  refine ⟨P, d, ?_⟩
  change MvPolynomial.map (algebraMap A K)
    (∑ i : Q.support, MvPolynomial.monomial i.val (hd i.val i.prop).choose) = _
  rw [map_sum]
  simp only [MvPolynomial.map_monomial]
  have hnum (i : Q.support) : algebraMap A K (hd i.val i.prop).choose =
      (d : A) • AddMonoidAlgebra.coeff Q i.val := (hd i.val i.prop).choose_spec
  simp_rw [hnum]
  simp_rw [← MvPolynomial.smul_monomial]
  rw [← Finset.smul_sum]
  congr 1
  exact (Finset.sum_coe_sort Q.support
    (fun i ↦ MvPolynomial.monomial i (AddMonoidAlgebra.coeff Q i))).trans
      Q.support_sum_monomial_coeff


-- Polynomial base change and tensoring a quotient commute with the same principal ideal.
private theorem polynomial_quotient_base_change
    {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]
    {σ : Type v} (P : MvPolynomial σ A) :
    Nonempty (K ⊗[A] (MvPolynomial σ A ⧸ Ideal.span {P}) ≃ₐ[K]
      MvPolynomial σ K ⧸ Ideal.span {MvPolynomial.map (algebraMap A K) P}) := by
  let e : K ⊗[A] MvPolynomial σ A ≃ₐ[K] MvPolynomial σ K :=
    MvPolynomial.algebraTensorAlgEquiv A K
  have hmap : Ideal.span {MvPolynomial.map (algebraMap A K) P} =
      (Ideal.span {P} |>.map (includeRight (A := K) (R := A))).map e := by
    change Ideal.span {MvPolynomial.map (algebraMap A K) P} =
      ((Ideal.span {P}).map (includeRight (A := K) (R := A)).toRingHom).map e.toRingEquiv.toRingHom
    rw [Ideal.map_map, Ideal.map_span]
    simp only [Set.image_singleton]
    congr 2
    change MvPolynomial.map (algebraMap A K) P = e (1 ⊗ₜ[A] P)
    simp [e]
  exact ⟨(tensorQuotientEquiv (R := A) K (MvPolynomial σ A) K (Ideal.span {P})).trans
    (Ideal.quotientEquivAlg _ _ e hmap)⟩


-- Apply Spec to the algebra equivalence and track the generic-fibre projection to the field.
private theorem generic_spec_iso {S : Scheme.{u}} [IsAffine S] (η : S) {B : Type u} [CommRing B]
    [Algebra Γ(S, ⊤) B] {Z : Type u} [CommRing Z]
    [Algebra (S.residueField η) Z]
    [Algebra Γ(S, ⊤) (S.residueField η)]
    (hφ : CommRingCat.ofHom (algebraMap Γ(S, ⊤) (S.residueField η)) = S.Γevaluation η)
    (e : (S.residueField η) ⊗[Γ(S, ⊤)] B ≃ₐ[S.residueField η] Z) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv
    let q := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) Z))
    ∃ i : g.fiber η ≅ Spec (.of Z), i.hom ≫ q = g.fiberToSpecResidueField η := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv
  let a := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B))
  let b := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (S.residueField η)))
  have hb : S.fromSpecResidueField η ≫ S.isoSpec.hom = b := by
    rw [Scheme.isoSpec_hom, Scheme.fromSpecResidueField, Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    change Spec.map (S.Γevaluation η) = b
    exact congrArg Spec.map hφ.symm
  let j := asIso (pullback.map g (S.fromSpecResidueField η) a b
    (𝟙 _) (𝟙 _) S.isoSpec.hom (by simp [g, a]) (by simpa using hb))
  let k := j ≪≫ pullbackSymmetry a b ≪≫
    pullbackSpecIso Γ(S, ⊤) (S.residueField η) B
  let l := Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op
  refine ⟨k ≪≫ l, ?_⟩
  change k.hom ≫ l.hom ≫ Spec.map
    (CommRingCat.ofHom (algebraMap (S.residueField η) Z)) = _
  have hl : l.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap (S.residueField η) Z)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField η) ((S.residueField η) ⊗[Γ(S, ⊤)] B))) := by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact e.symm.commutes x
  rw [hl]
  simp [k, j, Scheme.Hom.fiberToSpecResidueField,
    pullbackSpecIso_hom_fst', a, b, g]



/-- Every polynomial hypersurface over the generic residue field of an integral affine
scheme is the generic fibre of a polynomial hypersurface over its base sections.

Source: Stacks Project, Tag 0559, first proof, clearing coefficient denominators.
Proof: Identify K=kappa(eta) with the fraction field of A=Gamma(S,O_S), using that eta
is generic and S is integral affine. The finite support of Q has finitely many
coefficients in K. Multiply by the product d of their nonzero denominators; the resulting
polynomial P has coefficients in A. Since d is nonzero in K, (P_K)=(Q) in the polynomial
ring over K, including Q=0 (choose d=1 when its support is empty). Base change of the
coefficient-induced spectrum map identifies the generic fibre with Spec(K[t]/(P_K)).
The equality of principal ideals gives the displayed isomorphism with Spec(K[t]/(Q)).
All the maps are induced by coefficient maps, so the isomorphism commutes with the two
structure maps to Spec K. No integrality or irreducibility of Q is needed.

(blueprint: lem-sbc-generic-polynomial-hypersurface-descent) -/
theorem exists_base_hypersurface_of_generic_polynomial
    {S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (η : S) (hη : IsGenericPoint η Set.univ)
    {n : ℕ} (Q : MvPolynomial (Fin n) (S.residueField η)) :
    ∃ P : MvPolynomial (Fin n) Γ(S, ⊤),
      let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
      let g : H ⟶ S := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
      let Z := Spec (.of (MvPolynomial (Fin n) (S.residueField η) ⧸ Ideal.span {Q}))
      let q : Z ⟶ Spec (.of (S.residueField η)) := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C))
      ∃ i : g.fiber η ≅ Z, i.hom ≫ q = g.fiberToSpecResidueField η := by
  let : Algebra Γ(S, ⊤) (S.residueField η) := (S.Γevaluation η).hom.toAlgebra
  have : IsFractionRing Γ(S, ⊤) (S.residueField η) := fraction_at_generic η hη
  obtain ⟨P, d, hP⟩ := clear_polynomial (A := Γ(S, ⊤)) Q
  obtain ⟨ep⟩ := polynomial_quotient_base_change (K := S.residueField η) P
  have hspan : Ideal.span {MvPolynomial.map (algebraMap Γ(S, ⊤) (S.residueField η)) P} =
      Ideal.span {Q} := by
    rw [hP]
    have hs : (d : Γ(S, ⊤)) • Q =
        MvPolynomial.C (algebraMap Γ(S, ⊤) (S.residueField η) d) * Q := by
      rw [← MvPolynomial.smul_eq_C_mul]
      exact (IsScalarTower.algebraMap_smul (S.residueField η) (d : Γ(S, ⊤)) Q).symm
    rw [hs]
    exact Ideal.span_singleton_mul_left_unit
      ((IsLocalization.map_units (S.residueField η) d).map MvPolynomial.C) Q
  let er := ep.trans (Ideal.quotientEquivAlgOfEq (S.residueField η) hspan)
  obtain ⟨i, hi⟩ := generic_spec_iso η rfl er
  exact ⟨P, i, hi⟩

end AlgebraicGeometry
