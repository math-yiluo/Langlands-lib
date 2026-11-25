/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Bounded finite-free terms of the explicit scalar dual tensor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped DirectSum TensorProduct
namespace AlgebraicGeometry.ProEtale

private def dualEvaluation {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain P
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of R R)) n →ₗ[R]
      (P.X (-n) ⟶ ModuleCat.of R R) where
  toFun z := z.v (-n) 0 (by omega) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).hom
  map_add' x y := by simp [CochainComplex.HomComplex.Cochain.add_v, Preadditive.add_comp]
  map_smul' r x := by simp [CochainComplex.HomComplex.Cochain.smul_v, Linear.smul_comp]

private theorem dualEvaluation_bijective {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Bijective (dualEvaluation P n) := by
  constructor
  · intro z w h
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    by_cases hq : q = 0
    · subst hq
      have hp : p = -n := by omega
      subst hp
      exact (cancel_mono
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).hom).1 h
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ModuleCat.of R R) q hq).eq_of_tgt _ _
  · intro f
    refine ⟨CochainComplex.HomComplex.Cochain.single
      (f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (ModuleCat.of R R)).inv) n, ?_⟩
    change _ ≫ _ = f
    simp only [CochainComplex.HomComplex.Cochain.single_v, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

private def dualEvaluationEquiv {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (CochainComplex.moduleHomComplex P
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of R R))).X n ≃ₗ[R]
      (P.X (-n) →ₗ[R] R) :=
  (LinearEquiv.ofBijective (dualEvaluation P n) (dualEvaluation_bijective P n)).trans
    ModuleCat.homLinearEquiv

private theorem dualTerm_zero {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (h : IsZero (P.X (-n))) :
    IsZero ((CochainComplex.moduleHomComplex P
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of R R))).X n) := by
  have : Subsingleton (P.X (-n)) := ModuleCat.subsingleton_of_isZero h
  have : Subsingleton (P.X (-n) →ₗ[R] R) := inferInstance
  have := (dualEvaluationEquiv P n).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem tensorTerm_zero {R : Type u} [CommRing R]
    (D P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (h : ∀ p q : ℤ, p + q = n → IsZero (D.X p) ∨ IsZero (P.X q)) :
    IsZero ((CochainComplex.mapBifunctor D P (curriedTensor _)).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (D.X p ⊗ P.X q) := by
    rcases h p q hpq with hd | hp
    · exact Functor.map_isZero (tensorRight (P.X q)) hd
    · exact Functor.map_isZero (tensorLeft (D.X p)) hp
  exact hz.eq_of_src _ _

private theorem tensorTerm_free_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (D P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hD : ∀ p : ℤ, p < a ∨ b < p → IsZero (D.X p))
    (hfreeD : ∀ p : ℤ, Module.Free R (D.X p) ∧ Module.Finite R (D.X p))
    (hfreeP : ∀ q : ℤ, Module.Free R (P.X q) ∧ Module.Finite R (P.X q))
    (n : ℤ) :
    Module.Free R ((CochainComplex.mapBifunctor D P (curriedTensor _)).X n) ∧
      Module.Finite R ((CochainComplex.mapBifunctor D P (curriedTensor _)).X n) := by
  classical
  let I := {pq : ℤ × ℤ // pq.1 + pq.2 = n}
  let M : I → ModuleCat.{u} R := fun pq ↦ D.X pq.val.1 ⊗ P.X pq.val.2
  let (p : ℤ) : Module.Free R (D.X p) := (hfreeD p).1
  let (p : ℤ) : Module.Finite R (D.X p) := (hfreeD p).2
  let (p : ℤ) : Module.Free R (P.X p) := (hfreeP p).1
  let (p : ℤ) : Module.Finite R (P.X p) := (hfreeP p).2
  let (pq : I) : Module.Free R (M pq) := by
    change Module.Free R (D.X pq.val.1 ⊗[R] P.X pq.val.2)
    infer_instance
  let (pq : I) : Module.Finite R (M pq) := by
    change Module.Finite R (D.X pq.val.1 ⊗[R] P.X pq.val.2)
    infer_instance
  let S : I → Prop := fun pq ↦ a ≤ pq.val.1 ∧ pq.val.1 ≤ b
  have : Finite {pq : I // S pq} := by
    let f : {pq : I // S pq} → Set.Icc a b := fun pq ↦ ⟨pq.val.val.1, pq.property⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val h
    · have hp := congrArg Subtype.val h
      have hx := x.val.property
      have hy := y.val.property
      dsimp [f] at hp
      omega
  let restriction : (⨁ pq : I, M pq) →ₗ[R] (⨁ pq : {pq : I // S pq}, M pq.val) :=
    DFinsupp.subtypeDomainLinearMap R (fun pq : I ↦ M pq) S
  have hi : Function.Injective restriction := by
    intro x y h
    apply DFinsupp.ext
    intro pq
    by_cases hs : S pq
    · exact congrArg (fun z ↦ z ⟨pq, hs⟩) h
    · have hz : IsZero (M pq) := Functor.map_isZero (tensorRight (P.X pq.val.2))
        (hD pq.val.1 (by dsimp [S] at hs; omega))
      exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
  have : Module.Finite R (⨁ pq : I, M pq) := Module.Finite.of_injective restriction hi
  let e : ((CochainComplex.mapBifunctor D P (curriedTensor _)).X n) ≃ₗ[R]
      (⨁ pq : I, M pq) := (ModuleCat.coprodIsoDirectSum M).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The signed dual tensor of a bounded finite-free complex is bounded finite free.

Source: current blueprint, `proposition-local-structure-integral-constructible-complexes`,
Compatible isomorphisms, paragraph beginning These Hom groups can be infinite.
(blueprint: lem-pe-internal-perfect-dual-tensor-finite).

Proof: evaluation on the unique potentially nonzero target degree identifies the degree-r
term of Hom(P,A[0]) with the dual of P^(-r).  All other factors of the product are zero.
A basis of P^(-r) gives its finite dual basis. The dual vanishes outside [-b,-a].
The tensor's degree-k term is the direct sum over r+s=k; only -b<=r<=-a and a<=s<=b
can contribute. Delete the zero summands, leaving a finite sum of tensor products of
finite free modules, with the tensor-product bases. This is finite free and vanishes
outside [a-b,b-a]. These arguments apply to zero terms and to an empty interval as well. -/
theorem internalPerfectScalarDualTensor_finite
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ c d : ℤ, (internalPerfectScalarDualTensor l E P).IsStrictlyGE c ∧
      (internalPerfectScalarDualTensor l E P).IsStrictlyLE d ∧
      (∀ i : ℤ, Module.Free (Padic.coefficientExtensionIntegers l E)
          ((internalPerfectScalarDualTensor l E P).X i) ∧
        Module.Finite (Padic.coefficientExtensionIntegers l E)
          ((internalPerfectScalarDualTensor l E P).X i))  := by
  let R := Padic.coefficientExtensionIntegers l E
  let D := CochainComplex.moduleHomComplex P
    ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of R R))
  have hcoeff := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsPrincipalIdealRing R := hcoeff.2.2.2.2.2.2.2.2.1
  have hDzero (p : ℤ) (hp : p < -b ∨ -a < p) : IsZero (D.X p) := by
    apply dualTerm_zero
    rcases hp with hp | hp
    · exact P.isZero_of_isStrictlyLE b (-p) (by omega)
    · exact P.isZero_of_isStrictlyGE a (-p) (by omega)
  have hDfree (p : ℤ) : Module.Free R (D.X p) ∧ Module.Finite R (D.X p) := by
    have : Module.Finite R (P.X (-p)) := (_hfree (-p)).1
    have : Module.Free R (P.X (-p)) := (_hfree (-p)).2
    let e' : D.X p ≃ₗ[R] Module.Dual R (P.X (-p)) := dualEvaluationEquiv P p
    exact ⟨Module.Free.of_equiv e'.symm, Module.Finite.equiv e'.symm⟩
  refine ⟨a - b, b - a, ?_, ?_, ?_⟩
  · apply (CochainComplex.isStrictlyGE_iff _ _).2
    intro k hk
    apply tensorTerm_zero D P k
    intro p q hpq
    by_cases hp : p < -b
    · exact Or.inl (hDzero p (Or.inl hp))
    · exact Or.inr (P.isZero_of_isStrictlyGE a q (by omega))
  · apply (CochainComplex.isStrictlyLE_iff _ _).2
    intro k hk
    apply tensorTerm_zero D P k
    intro p q hpq
    by_cases hp : -a < p
    · exact Or.inl (hDzero p (Or.inr hp))
    · exact Or.inr (P.isZero_of_isStrictlyLE b q (by omega))
  · exact tensorTerm_free_finite D P (-b) (-a) hDzero hDfree
      (fun q ↦ ⟨(_hfree q).2, (_hfree q).1⟩)

end AlgebraicGeometry.ProEtale
