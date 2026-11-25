/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Tensor products of finite type domains over an algebraically closed field

Source: Stacks Project, Algebra, Lemma 00I7, final paragraph
(blueprint: lem-weil-pbc-algclosed-finite-type-tensor-domain).
-/

@[expose] public section

universe u v w
open scoped TensorProduct

/-- A domain tensored with a finite type domain over an algebraically closed field is a domain.
Source: Stacks Project, Algebra, Lemma 00I7, final paragraph
(blueprint: lem-weil-pbc-algclosed-finite-type-tensor-domain).

Proof: Choose a basis of the first domain as a vector space over the base field and
express both proposed zero divisors in coordinates in the second domain. At a maximal
ideal of the second domain, the residue field is finite over the base by the
Nullstellensatz, and is therefore equal to the algebraically closed base field. The
specialized tensor product is isomorphic to the first domain, so one specialized factor
vanishes. Thus the product of any coordinate of the first element with any coordinate of
the second lies in every maximal ideal of the second domain. That domain is Jacobson,
so these products vanish. If both tensor elements were nonzero, each would have a nonzero
coordinate and their product would contradict the domain property of the second factor.
Finally, tensor products of two domains over a field are nonzero (the base field injects
into both factors), so absence of zero divisors gives a domain -/
theorem IsAlgClosed.isDomain_tensorProduct_of_finiteType
    (k : Type u) [Field k] [IsAlgClosed k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]
    (S : Type w) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S] :
    IsDomain (R ⊗[k] S) := by
  classical
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  let b := Module.Free.chooseBasis k R
  let Φ (C : Type _) [CommRing C] [Algebra k C]
      (i : Module.Free.ChooseBasisIndex k R) : R ⊗[k] C →ₗ[k] C :=
    (((Algebra.TensorProduct.basis C b).coord i).restrictScalars k).comp
      (TensorProduct.comm k R C).toLinearMap
  have hΦ (C : Type _) [CommRing C] [Algebra k C]
      (x : R ⊗[k] C) (hx : ∀ i, Φ C i x = 0) : x = 0 := by
    have := ((Algebra.TensorProduct.basis C b).forall_coord_eq_zero_iff
      (x := TensorProduct.comm k R C x)).mp hx
    simpa using this
  have hnat (C : Type _) [CommRing C] [Algebra k C]
      (π : S →ₐ[k] C) (i) (x : R ⊗[k] S) :
      π (Φ S i x) = Φ C i (Algebra.TensorProduct.map (AlgHom.id k R) π x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul a c => simp [Φ, Algebra.TensorProduct.basis_repr_tmul]
  have hzero (x y : R ⊗[k] S) (hxy : x * y = 0) : x = 0 ∨ y = 0 := by
    have hpt (m : Ideal S) [m.IsMaximal] :
        (∀ i, Φ S i x ∈ m) ∨ ∀ i, Φ S i y ∈ m := by
      let κ := S ⧸ m
      let : Field κ := Ideal.Quotient.field m
      have : Algebra.FiniteType k κ :=
        Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
          Ideal.Quotient.mk_surjective
      have : Module.Finite k κ := finite_of_finite_type_of_isJacobsonRing k κ
      let e : κ ≃ₐ[k] k :=
        (AlgEquiv.ofBijective (Algebra.ofId k κ)
          (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))).symm
      let f : R ⊗[k] κ ≃ₐ[k] R :=
        (Algebra.TensorProduct.congr (.refl) e).trans
          (Algebra.TensorProduct.rid k k R)
      have : IsDomain (R ⊗[k] κ) := f.toRingEquiv.isDomain
      let π := Ideal.Quotient.mkₐ k m
      let ψ := Algebra.TensorProduct.map (AlgHom.id k R) π
      have hmem (z : R ⊗[k] S) (hz : ψ z = 0) (i) : Φ S i z ∈ m := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change π _ = 0
        rw [hnat κ π i z, hz, map_zero]
      have hxy' : ψ x * ψ y = 0 := by rw [← map_mul, hxy, map_zero]
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hxy').imp (hmem x) (hmem y)
    by_contra! H
    obtain ⟨i, hi⟩ : ∃ i, Φ S i x ≠ 0 := by
      by_contra! h
      exact H.1 (hΦ S x h)
    obtain ⟨j, hj⟩ : ∃ j, Φ S j y ≠ 0 := by
      by_contra! h
      exact H.2 (hΦ S y h)
    have hjac : Φ S i x * Φ S j y ∈ (⊥ : Ideal S).jacobson := by
      rw [Ideal.jacobson, Submodule.mem_sInf]
      rintro m ⟨-, hm⟩
      rcases hpt m with h | h
      · exact Ideal.mul_mem_right _ m (h i)
      · exact Ideal.mul_mem_left m _ (h j)
    rw [IsJacobsonRing.out' _ Ideal.isRadical_bot, Ideal.mem_bot] at hjac
    exact mul_ne_zero hi hj hjac
  have : NoZeroDivisors (R ⊗[k] S) := ⟨fun {x y} ↦ hzero x y⟩
  have : Nontrivial (R ⊗[k] S) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k R S
      (algebraMap k R).injective (algebraMap k S).injective
  exact (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨inferInstance, inferInstance⟩
