/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Algebra.Ring.ULift

/-! # Characteristic polynomial of a locally free module
Source: literature/stacks-project/more-algebra.tex, Lemma Tag 09XI
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem charpoly_tower
    {A S T M : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    [AddCommGroup M] [Module A M] {n : ℕ}
    (b : Module.Basis (Fin n) S (S ⊗[A] M))
    (e : Module.Basis (Fin n) T (T ⊗[A] M)) (φ : M →ₗ[A] M) :
    (LinearMap.toMatrix b b (φ.baseChange S)).charpoly.map (algebraMap S T) =
      (LinearMap.toMatrix e e (φ.baseChange T)).charpoly := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis e
  have := Module.Finite.of_basis e
  let L := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix,
    ← LinearMap.charpoly_baseChange, LinearMap.baseChange_baseChange]
  change (L.symm.conj (φ.baseChange T)).charpoly = _
  exact LinearEquiv.charpoly_conj _ _

/-- Local characteristic polynomials agree on overlaps of the standard cover.
Source: Stacks Tag 09XI, proof of (3)⇒(1), last paragraph.
Proof: in A[1/(ab)], both a and b are units. Factor the map from A through
A[1/a] and A[1/b]. Base change the given bases along these factorizations.
Tensor-product cancellation identifies both resulting free modules with
A[1/(ab)] ⊗ M and both endomorphisms with the scalar extension of φ.
Scalar-extension compatibility of the free characteristic polynomial identifies
each mapped local polynomial with the characteristic polynomial in the
corresponding transported basis. Basis independence makes these equal.
This proof also holds for zero rings, a = b, and rank zero.
-/
private theorem charpoly_standardCover_overlap
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    {n r : ℕ} (f : Fin r → A)
    (b : ∀ a : Set.range f, Module.Basis (Fin n) (Localization.Away a.val)
      (Localization.Away a.val ⊗[A] M))
    (φ : M →ₗ[A] M) (a c : Set.range f) :
    ((LinearMap.toMatrix (b a) (b a) (φ.baseChange (Localization.Away a.val))).charpoly.map
      (IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (a.val * c.val)) a.val c.val)) =
    ((LinearMap.toMatrix (b c) (b c) (φ.baseChange (Localization.Away c.val))).charpoly.map
      (IsLocalization.Away.awayToAwayLeft
        (P := Localization.Away (a.val * c.val)) c.val a.val)) := by
  classical
  let T := Localization.Away (a.val * c.val)
  let q : Localization.Away a.val →+* T := IsLocalization.Away.awayToAwayRight (P := T) a.val c.val
  let q' : Localization.Away c.val →+* T := IsLocalization.Away.awayToAwayLeft (P := T) c.val a.val
  obtain ⟨e⟩ : Nonempty (Module.Basis (Fin n) T (T ⊗[A] M)) := by
    let : Algebra (Localization.Away a.val) T := q.toAlgebra
    have : IsScalarTower A (Localization.Away a.val) T :=
      IsScalarTower.of_algebraMap_eq fun x ↦
        (IsLocalization.Away.awayToAwayRight_eq
          (S := Localization.Away a.val) (P := T) a.val c.val x).symm
    exact ⟨((b a).baseChange T).map
      (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A
        (Localization.Away a.val) T T M)⟩
  change (LinearMap.toMatrix (b a) (b a) _).charpoly.map q =
    (LinearMap.toMatrix (b c) (b c) _).charpoly.map q'
  calc
    _ = (LinearMap.toMatrix e e (φ.baseChange T)).charpoly := by
      let : Algebra (Localization.Away a.val) T := q.toAlgebra
      have : IsScalarTower A (Localization.Away a.val) T :=
        IsScalarTower.of_algebraMap_eq fun x ↦
          (IsLocalization.Away.awayToAwayRight_eq
          (S := Localization.Away a.val) (P := T) a.val c.val x).symm
      exact charpoly_tower (b a) e φ
    _ = _ := by
      let : Algebra (Localization.Away c.val) T := q'.toAlgebra
      have : IsScalarTower A (Localization.Away c.val) T :=
        IsScalarTower.of_algebraMap_eq fun x ↦
          (IsLocalization.Away.awayToAwayLeft_eq
          (S := Localization.Away c.val) (P := T) c.val a.val x).symm
      exact (charpoly_tower (b c) e φ).symm

/-- Glue the characteristic polynomials on a standard localization cover.
Source: Stacks Tag 09XI, proof of (3)⇒(1), last paragraph; Tag 00EJ.
Proof: compare the two local matrices after scalar extension to A[1/(fᵢfⱼ)].
The tensor-product cancellation equivalence identifies both endomorphisms;
basis invariance and scalar-extension compatibility of the free characteristic
polynomial show that the polynomials agree on overlaps. For each k < n, glue
their k-th coefficients uniquely by Tag 00EJ. The coefficients at n are all 1
and those above n all vanish, by the matrix characteristic-polynomial formula.
Thus X^n plus the sum of the glued lower coefficients has exactly the required
images, by coefficientwise equality. This also works for n = 0 and for the
empty cover, which forces the base ring to be zero.
-/
private theorem charpoly_standardCover_glue
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (b : ∀ a : Set.range f, Module.Basis (Fin n) (Localization.Away a.val)
      (Localization.Away a.val ⊗[A] M))
    (φ : M →ₗ[A] M) :
    ∃ χ : Polynomial A,
      (∀ a : Set.range f, χ.map (algebraMap A (Localization.Away a.val)) =
      (LinearMap.toMatrix (b a) (b a) (φ.baseChange (Localization.Away a.val))).charpoly) ∧
      ∃ c : Fin n → A,
        χ = Polynomial.X ^ n +
          ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ) := by
  classical
  let p (a : Set.range f) :=
    (LinearMap.toMatrix (b a) (b a) (φ.baseChange (Localization.Away a.val))).charpoly
  have hcompat (k : ℕ) (a c : Set.range f) :
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (a.val * c.val)) a.val c.val ((p a).coeff k) =
      IsLocalization.Away.awayToAwayLeft
        (P := Localization.Away (a.val * c.val)) c.val a.val ((p c).coeff k) := by
    have h := congrArg (fun q ↦ q.coeff k) (charpoly_standardCover_overlap f b φ a c)
    simpa only [Polynomial.coeff_map] using h
  choose c hc using fun k : Fin n ↦
    (Localization.existsUnique_algebraMap_eq_of_span_eq_top (Set.range f) hgen
      (fun a ↦ (p a).coeff (k : ℕ)) (hcompat k)).exists
  refine ⟨Polynomial.X ^ n +
    ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ), ?_, c, rfl⟩
  intro a
  have hexp : p a = Polynomial.X ^ n +
      ∑ k : Fin n, Polynomial.C ((p a).coeff (k : ℕ)) * Polynomial.X ^ (k : ℕ) := by
    by_cases ht : Subsingleton (Localization.Away a.val)
    · have := ht
      exact Subsingleton.elim _ _
    have := not_subsingleton_iff_nontrivial.mp ht
    have hm := (LinearMap.toMatrix (b a) (b a)
      (φ.baseChange (Localization.Away a.val))).charpoly_monic.as_sum
    rw [Fin.sum_univ_eq_sum_range
      (fun k ↦ Polynomial.C ((p a).coeff k) * Polynomial.X ^ k) n]
    simpa only [p, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using hm
  change Polynomial.map _ _ = p a
  rw [hexp]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, hc]

/-- The scalar-extension property is equivalent to its identities on a standard cover.
Source: Stacks Tag 09XI, proof of (3)⇒(1), last paragraph, and Tag 00EJ.
Proof: in the forward direction apply the scalar-extension property to the
localization at each fᵢ, lifted to Type (max u w) by ULift. Transport the given
basis along scalar lifting and descend the polynomial equality along the
injective ULift ring equivalence. In the reverse direction fix A → A′ and a
basis of A′ ⊗ M. The images of fᵢ still span the unit ideal. Localize A′ at each
image of fᵢ. Factor A → A′[1/fᵢ] through A[1/fᵢ]. Tensor-product cancellation
identifies the scalar extensions of both endomorphisms. Basis independence
and scalar-extension compatibility of matrix characteristic polynomials give
the desired equality in each such localization. Injectivity of the standard
cover, applied to every coefficient, gives equality over A′. Neither argument
requires a nonzero ring or a positive rank.
-/
private theorem charpoly_standardCover_comparison
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (b : ∀ a : Set.range f, Module.Basis (Fin n) (Localization.Away a.val)
      (Localization.Away a.val ⊗[A] M))
    (φ : M →ₗ[A] M) (χ : Polynomial A) :
    (let P : Polynomial A → Prop := fun χ ↦
      ∀ (A' : Type (max u w)) [CommRing A'] (ρ : A →+* A'),
        let : Algebra A A' := RingHom.toAlgebra ρ;
        ∀ e : Module.Basis (Fin n) A' (A' ⊗[A] M),
          χ.map ρ = (LinearMap.toMatrix e e (φ.baseChange A')).charpoly;
    P χ) ↔
    (∀ a : Set.range f, χ.map (algebraMap A (Localization.Away a.val)) =
      (LinearMap.toMatrix (b a) (b a) (φ.baseChange (Localization.Away a.val))).charpoly) := by
  classical
  dsimp only
  constructor
  · intro hP a
    let S := Localization.Away a.val
    let T := ULift.{w} S
    let q : S →+* T := ULift.ringEquiv.symm.toRingHom
    let ρ := q.comp (algebraMap A S)
    let : Algebra S T := q.toAlgebra
    let : Algebra A T := ρ.toAlgebra
    let : Module S T := Algebra.toModule
    let : Module A T := Algebra.toModule
    let : SMul S T := (inferInstance : Module S T).toSMul
    let : SMul A T := (inferInstance : Module A T).toSMul
    have : IsScalarTower A S T :=
      IsScalarTower.of_algebraMap_eq (R := A) (S := S) (A := T) fun x ↦ rfl
    let e := ((b a).baseChange T).map
      (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M)
    apply Polynomial.map_injective q ULift.ringEquiv.symm.injective
    rw [Polynomial.map_map]
    exact (hP T ρ e).trans (charpoly_tower (b a) e φ).symm
  · intro hlocal A' _ ρ
    let : Algebra A A' := ρ.toAlgebra
    intro e
    have hgen' : Ideal.span (Set.range (fun i ↦ ρ (f i))) = ⊤ := by
      rw [Set.range_comp', ← Ideal.map_span, hgen, Ideal.map_top]
    have hloc (i : Fin r) :
        χ.map (algebraMap A (Localization.Away (ρ (f i)))) =
        (LinearMap.toMatrix e e (φ.baseChange A')).charpoly.map
          (algebraMap A' (Localization.Away (ρ (f i)))) := by
      let a : Set.range f := ⟨f i, ⟨i, rfl⟩⟩
      let S := Localization.Away (f i)
      let T := Localization.Away (ρ (f i))
      let q : S →+* T := IsLocalization.Away.lift (f i)
        (show IsUnit (algebraMap A T (f i)) from by
          change IsUnit (algebraMap A' T (ρ (f i)))
          exact IsLocalization.Away.algebraMap_isUnit (ρ (f i)))
      let eT := (e.baseChange T).map
        (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A A' T T M)
      have hc : q.comp (algebraMap A S) = algebraMap A T := by
        ext x
        simp only [RingHom.comp_apply, q, IsLocalization.Away.lift_eq]
      have hleft : χ.map (algebraMap A T) =
          (LinearMap.toMatrix eT eT (φ.baseChange T)).charpoly := by
        let : Algebra S T := q.toAlgebra
        have : IsScalarTower A S T :=
          IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.congr_fun hc x).symm
        rw [← hc, ← Polynomial.map_map, hlocal a]
        exact charpoly_tower (b a) eT φ
      exact hleft.trans (charpoly_tower e eT φ).symm
    ext k
    apply Localization.algebraMap_injective_of_span_eq_top
      (Set.range (fun i ↦ ρ (f i))) hgen'
    funext ⟨a, ha⟩
    obtain ⟨i, rfl⟩ := ha
    change algebraMap A' (Localization.Away (ρ (f i))) ((χ.map ρ).coeff k) =
      algebraMap A' (Localization.Away (ρ (f i)))
        ((LinearMap.toMatrix e e (φ.baseChange A')).charpoly.coeff k)
    have h := congrArg (fun p ↦ p.coeff k) (hloc i)
    simp only [Polynomial.coeff_map] at h
    rw [IsScalarTower.algebraMap_apply A A' (Localization.Away (ρ (f i)))] at h
    simpa only [Polynomial.coeff_map, RingHom.algebraMap_toAlgebra] using h


set_option linter.unusedVariables false in
/-- Existence and uniqueness of the characteristic polynomial on a finite locally free module.
Source: literature/stacks-project/more-algebra.tex, Lemma Tag 09XI, proof of (3)⇒(1).
1. Use `lem-weil-pbc-localization-module-tensor` to identify each localized endomorphism
with scalar extension. In a local basis take its matrix characteristic polynomial
(`def-weil-pbc-charpoly-free-module`); basis independence and the monic expansion follow
from `lem-weil-pbc-charpoly-free-module-properties` (a), (c).
2. For any ring map inverting a cover element, factor through its localization and use
`lem-weil-pbc-module-base-change-transitive` and the localization-tensor comparison.
Naturality and free characteristic-polynomial properties (b), (d) identify the resulting
characteristic polynomial with the image of the local one.
3. Apply this comparison twice over the localization at the product of two cover elements.
The two local polynomials agree there, hence so do all their coefficients.
4. Glue each coefficient uniquely by `lem-weil-pbc-standard-covering-glue` (ii).
Uniqueness forces coefficients above n to vanish and the coefficient at n to be one.
These coefficients define the displayed polynomial, restricting to every local polynomial.
5. After any base change where the module is free, the images of the cover elements still
generate the unit ideal. Over their localizations, transitive base change and free
characteristic-polynomial properties compare both polynomials with the local ones.
Coefficientwise injectivity in `lem-weil-pbc-standard-covering-glue` (i) gives equality.
6. Any other polynomial with the base-change property restricts to the same local
polynomials. Apply the same coefficientwise injectivity to obtain uniqueness.
7. In the free case take the identity ring map, identify scalar extension with the original
module, and use free characteristic-polynomial properties (b) to obtain the usual polynomial.
-/
theorem charpoly_locallyFree_exists_unique
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      ∃ e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (φ : M →ₗ[A] M) :
    let P : Polynomial A → Prop := fun χ ↦
      ∀ (A' : Type (max u w)) [CommRing A'] (ρ : A →+* A'),
        letI : Algebra A A' := RingHom.toAlgebra ρ;
        ∀ e : Module.Basis (Fin n) A' (A' ⊗[A] M),
          χ.map ρ = (LinearMap.toMatrix e e (φ.baseChange A')).charpoly;
    ∃ χ : Polynomial A,
      (P χ ∧ ∀ χ' : Polynomial A, P χ' → χ' = χ) ∧
      (∃ c : Fin n → A,
        χ = Polynomial.X ^ n +
          ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)) ∧
      ((Nonempty (Module.Basis (Fin n) A M)) →
        ∀ e : Module.Basis (Fin n) A M,
          χ = (LinearMap.toMatrix e e φ).charpoly) := by
  classical
  let b : ∀ a : Set.range f, Module.Basis (Fin n) (Localization.Away a.val)
      (Localization.Away a.val ⊗[A] M) := fun a ↦ Classical.choice (by
    obtain ⟨a, ha⟩ := a
    obtain ⟨i, rfl⟩ := ha
    exact ⟨(hfree i).choose.map
      (LocalizedModule.isBaseChange (Submonoid.powers (f i)) M).equiv.symm⟩)
  obtain ⟨χ, hχ, c, hc⟩ := charpoly_standardCover_glue f hgen b φ
  have hP := (charpoly_standardCover_comparison.{u, v, w} f hgen b φ χ).2 hχ
  refine ⟨χ, ⟨hP, ?_⟩, ⟨c, hc⟩, ?_⟩
  · intro χ' hP'
    have hχ' := (charpoly_standardCover_comparison.{u, v, w} f hgen b φ χ').1 hP'
    ext k
    apply Localization.algebraMap_injective_of_span_eq_top (Set.range f) hgen
    funext a
    have h := congrArg (fun p : Polynomial (Localization.Away a.val) ↦ p.coeff k)
      ((hχ' a).trans (hχ a).symm)
    change algebraMap A (Localization.Away a.val) (χ'.coeff k) =
      algebraMap A (Localization.Away a.val) (χ.coeff k)
    simpa only [Polynomial.coeff_map] using h
  · intro _ e
    have hP₀ := (charpoly_standardCover_comparison.{u, v, 0} f hgen b φ χ).2 hχ
    let e' := e.map (_root_.TensorProduct.lid A M).symm
    have heq := hP₀ A (RingHom.id A) e'
    have hm : LinearMap.toMatrix e' e' (φ.baseChange A) =
        LinearMap.toMatrix e e φ := by
      simp only [e', LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
      congr 1
      ext m
      simp
    simpa only [Polynomial.map_id, hm] using heq

end Algebra
