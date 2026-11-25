/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import Mathlib.RingTheory.Extension.Presentation.Basic
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension

/-!
# Base change of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma Tag 00SS, part (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-base-change).
-/

@[expose] public section

universe u v

open scoped TensorProduct
namespace Algebra

/-- The base-changed naive presentation identifies the quotient by the mapped relations with
scalar extension of the original quotient, sending each variable to its pure tensor.
Proof: use `Presentation.baseChange`, identify its relation ideal with its kernel, and apply
`Presentation.quotientEquiv`. The variable formula is `aeval_X` for the base-changed generators.
Source: Stacks Project, Algebra, Lemma Tag 00SS, part (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-base-change). -/
private theorem polynomialQuotient_baseChange
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R']
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    ∃ e :
        (MvPolynomial (Fin n) R' ⧸
            Ideal.span (Set.range (fun i ↦ MvPolynomial.map (algebraMap R R') (f i))))
          ≃ₐ[R']
          (R' ⊗[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))),
      ∀ j : Fin n,
        e (Ideal.Quotient.mk (Ideal.span (Set.range
          (fun i ↦ MvPolynomial.map (algebraMap R R') (f i)))) (MvPolynomial.X j)) =
          (1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j)) := by
  classical
  -- The base-changed naive presentation has precisely the mapped relations.
  let P := (Presentation.naive (v := f)).baseChange R'
  let e := (Ideal.quotientEquivAlgOfEq R' P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars R')
  refine ⟨e, ?_⟩
  intro j
  change P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.X j)) = _
  change P.quotientEquiv (algebraMap P.Ring P.Quotient (MvPolynomial.X j)) = _
  rw [AlgEquiv.commutes]
  rw [Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_X]
  rfl

/-- Let `R → R'` be a ring map and `f₁, …, f_c ∈ R[x₁, …, xₙ]`, with images `f'ᵢ` in
`R'[x₁, …, xₙ]`. (a) The `R'`-algebra map `R'[x]/(f') → R' ⊗_R R[x]/(f)` with
`xⱼ ↦ 1 ⊗ xⱼ` is an isomorphism; (b) if `R[x]/(f)` is a relative global complete
intersection over `R`, so is `R'[x]/(f')` over `R'`.
Proof: (a) both sides corepresent the same functor on `R'`-algebras (tuples in the zero
locus of the `f'ᵢ`), by right exactness of the tensor product. (b) By (a), the fibre ring of
`R'[x]/(f')` at a prime `𝔮` of `R'` lying over `𝔭` is `κ(𝔮) ⊗_{κ(𝔭)}` the fibre ring of
`R[x]/(f)` at `𝔭`; it is nonzero exactly when the latter is, and its dimension is the same
because dimension of finite type algebras over a field is preserved under field extension
(Tag 00P3).
Source: Stacks Project, Algebra, Lemma Tag 00SS, part (1)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-base-change).
-/
theorem relativeGlobalCompleteIntersection_baseChange
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R']
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R) :
    (∃ e :
        (MvPolynomial (Fin n) R' ⧸
            Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap R R') (f i))))
          ≃ₐ[R']
          (R' ⊗[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))),
      ∀ j : Fin n,
        e (Ideal.Quotient.mk (Ideal.span (Set.range
          (fun i => MvPolynomial.map (algebraMap R R') (f i)))) (MvPolynomial.X j)) =
          (1 : R') ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j))) ∧
      (IsRelativeGlobalCompleteIntersectionPresentation f →
        IsRelativeGlobalCompleteIntersectionPresentation
          (fun i => MvPolynomial.map (algebraMap R R') (f i))) := by
  constructor
  · exact polynomialQuotient_baseChange R R' n c f
  · intro h q hq hnontrivial
    classical
    let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
    let S' := MvPolynomial (Fin n) R' ⧸ Ideal.span
      (Set.range (fun i ↦ MvPolynomial.map (algebraMap R R') (f i)))
    -- Contract the prime and use the canonical map of residue fields.
    let p := q.comap (algebraMap R R')
    have : p.IsPrime := Ideal.comap_isPrime _ _
    let k := p.ResidueField
    let K := q.ResidueField
    let : Algebra k K := (Ideal.ResidueField.map p q (algebraMap R R') rfl).toAlgebra
    let : Algebra R K := ((algebraMap R' K).comp (algebraMap R R')).toAlgebra
    have : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
    have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun r ↦ by
      exact (Ideal.ResidueField.map_algebraMap p q (algebraMap R R') rfl r).symm
    obtain ⟨e, _⟩ := polynomialQuotient_baseChange R R' n c f
    -- Tensor the presentation isomorphism, then cancel each intermediate base.
    let e₁ : q.Fiber S' ≃ₐ[K] K ⊗[R'] (R' ⊗[R] S) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
    let e₂ := Algebra.TensorProduct.cancelBaseChange R R' K K S
    let e₃ := Algebra.TensorProduct.cancelBaseChange R k K K S
    let E : q.Fiber S' ≃ₐ[K] K ⊗[k] (p.Fiber S) := e₁.trans (e₂.trans e₃.symm)
    have : Nontrivial (q.Fiber S') := hnontrivial
    have : Nontrivial (K ⊗[k] (p.Fiber S)) := E.symm.toEquiv.nontrivial
    -- A zero original fibre would have zero scalar extension.
    have : Nontrivial (p.Fiber S) := by
      by_contra hn
      have : Subsingleton (p.Fiber S) := not_nontrivial_iff_subsingleton.mp hn
      exact zero_ne_one (Subsingleton.elim (0 : K ⊗[k] (p.Fiber S)) 1)
    obtain ⟨hc, hdim⟩ := h p inferInstance
    refine ⟨hc, ?_⟩
    -- Transfer dimension across the fibre equivalence and the field extension.
    let H := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
    rw [IsHomeomorph.topologicalKrullDim_eq H H.isHomeomorph]
    have : Algebra.FinitePresentation k (p.Fiber S) :=
      ((Presentation.naive (v := f)).baseChange k).finitePresentation_of_isFinite
    have : Algebra.FiniteType k (p.Fiber S) := inferInstance
    exact (AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension
      k K (p.Fiber S)).trans hdim

end Algebra
