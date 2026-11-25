/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Idempotents of tensor products over a separably closed field

Let `k` be a separably closed field and `A` a `k`-algebra whose only idempotents are `0` and
`1`. We show that the same holds for `A ⊗[k] L` for every `k`-domain `L`. This is the algebraic
input for the fact that a connected scheme over a separably closed field is geometrically
connected (Stacks, Algebra, Lemma 10.48.4).

## Main statements

- `IsSepClosed.eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct`: if `k` is separably
  closed, `A` has no nontrivial idempotents and `L` is a `k`-domain, then `A ⊗[k] L` has no
  nontrivial idempotents.
- `IsSepClosed.exists_isSeparable_pow_and_isPurelyInseparable`: an algebraic extension of a
  separably closed field is purely inseparable (blueprint `lemma-representability-picard-functor`).
- `isPurelyInseparable_iff_exists_algebraMap_eq_pow`: `E / F` is purely inseparable iff every
  `α ∈ E` has `α ^ (q ^ n) ∈ F` for some `n` (blueprint `def-pc-field-tower`).
-/

@[expose] public section

open TensorProduct

namespace IsSepClosed

variable {k A : Type*} [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]

/-- Over a separably closed field `k`, tensoring a `k`-algebra `A` without nontrivial idempotents
with a finitely generated `k`-domain `B` creates no nontrivial idempotents.

At a maximal ideal `m` of `B` the residue field `B ⧸ m` is finite, hence purely inseparable,
over `k`, so the image of an idempotent `e` in `A ⊗[k] (B ⧸ m)` comes from `A` and is `0`
or `1`: all coordinates of `e` or all coordinates of `1 - e` (with respect to a `k`-basis of
`A`) lie in `m`. If `e ≠ 0, 1`, the product of a nonzero coordinate of `e` and a nonzero
coordinate of `1 - e` thus lies in every maximal ideal of the Jacobson domain `B`, so it is
zero, a contradiction. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct_of_finiteType
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) {e : A ⊗[k] B}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  let b := Module.Free.chooseBasis k A
  -- the coordinates of an element of `A ⊗[k] C` with respect to the basis `b` of `A`
  let Φ (C : Type _) [CommRing C] [Algebra k C] (i : Module.Free.ChooseBasisIndex k A) :
      A ⊗[k] C →ₗ[k] C :=
    (((Algebra.TensorProduct.basis C b).coord i).restrictScalars k).comp
      (TensorProduct.comm k A C).toLinearMap
  have hΦ (C : Type _) [CommRing C] [Algebra k C] (x : A ⊗[k] C) (hx : ∀ i, Φ C i x = 0) :
      x = 0 := by
    have := ((Algebra.TensorProduct.basis C b).forall_coord_eq_zero_iff
      (x := TensorProduct.comm k A C x)).mp hx
    simpa using this
  have hnat (C : Type _) [CommRing C] [Algebra k C] (π : B →ₐ[k] C) (i) (x : A ⊗[k] B) :
      π (Φ B i x) = Φ C i (Algebra.TensorProduct.map (AlgHom.id k A) π x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul a c =>
      simp [Φ, Algebra.TensorProduct.basis_repr_tmul]
  -- at every closed point, `e` specialises to `0` or `1`
  have hpt (m : Ideal B) [m.IsMaximal] :
      (∀ i, Φ B i e ∈ m) ∨ ∀ i, Φ B i (1 - e) ∈ m := by
    let κ := B ⧸ m
    let : Field κ := Ideal.Quotient.field m
    have : Algebra.FiniteType k κ :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
        Ideal.Quotient.mk_surjective
    have : Module.Finite k κ := finite_of_finite_type_of_isJacobsonRing k κ
    let π : B →ₐ[k] κ := Ideal.Quotient.mkₐ k m
    let e' := Algebra.TensorProduct.map (AlgHom.id k A) π e
    have he' : IsIdempotentElem e' := he.map _
    obtain ⟨n, hn, a, ha⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (k := k)
      (K := κ) e'
    have hpow : e' ^ n = e' := he'.pow_eq hn.ne'
    rw [hpow] at ha
    have hinj : Function.Injective (algebraMap A (A ⊗[k] κ)) :=
      Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k κ).injective
    have haid : IsIdempotentElem a := hinj (by rw [map_mul, ha]; exact he')
    have hmem (x : A ⊗[k] B) (hx : Algebra.TensorProduct.map (AlgHom.id k A) π x = 0) (i) :
        Φ B i x ∈ m := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change π _ = 0
      rw [hnat κ π i x, hx, map_zero]
    rcases hA a haid with rfl | rfl
    · exact .inl (hmem e (by change e' = 0; rw [← ha]; simp))
    · refine .inr (hmem _ ?_)
      rw [map_sub, map_one]
      change 1 - e' = 0
      rw [← ha, map_one, sub_self]
  by_contra! H
  obtain ⟨i, hi⟩ : ∃ i, Φ B i e ≠ 0 := by
    by_contra! h; exact H.1 (hΦ B e h)
  obtain ⟨j, hj⟩ : ∃ j, Φ B j (1 - e) ≠ 0 := by
    by_contra! h; exact H.2 (sub_eq_zero.mp (hΦ B _ h)).symm
  have hjac : Φ B i e * Φ B j (1 - e) ∈ (⊥ : Ideal B).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    rcases hpt m with h | h
    · exact Ideal.mul_mem_right _ m (h i)
    · exact Ideal.mul_mem_left m _ (h j)
  rw [IsJacobsonRing.out' _ Ideal.isRadical_bot, Ideal.mem_bot] at hjac
  exact mul_ne_zero hi hj hjac

/-- Over a separably closed field `k`, tensoring a `k`-algebra `A` without nontrivial idempotents
with a `k`-domain `L` (e.g. a field extension) creates no nontrivial idempotents. An idempotent
of `A ⊗[k] L` already lives in `A ⊗[k] B` for a finitely generated `k`-subalgebra `B` of `L`. -/
@[stacks 037U "Stated in terms of idempotents."]
theorem eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct
    {L : Type*} [CommRing L] [IsDomain L] [Algebra k L]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) {e : A ⊗[k] L}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset e
  let B := Algebra.adjoin k (S.image Prod.snd : Set L)
  have : Algebra.FiniteType k B :=
    (Subalgebra.fg_iff_finiteType B).mp (Subalgebra.fg_adjoin_finset _)
  let ι := Algebra.TensorProduct.map (AlgHom.id k A) B.val
  have hι : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A) B.val.toLinearMap
      Subtype.val_injective
  have hmem (x : A × L) (hx : x ∈ S) : x.2 ∈ B :=
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
  let e' : A ⊗[k] B := ∑ x ∈ S.attach, x.1.1 ⊗ₜ ⟨x.1.2, hmem _ x.2⟩
  have he' : ι e' = ∑ x ∈ S, x.1 ⊗ₜ x.2 := by
    simp only [e', map_sum, ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Subalgebra.coe_val]
    exact Finset.sum_attach S fun x ↦ x.1 ⊗ₜ x.2
  rw [← he'] at he ⊢
  have he'' : IsIdempotentElem e' := hι (by rw [map_mul]; exact he)
  rcases eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct_of_finiteType hA he'' with h | h
  · simp [h]
  · simp [h]

end IsSepClosed

section KBar

universe u v

variable (k : Type u) [Field k]

/-- **The algebraic closure of a separably closed field is purely inseparable.** Let `k` be
separably closed of exponential characteristic `p` and `K / k` algebraic (for instance
`K = k̄`). Every `α ∈ K` has a power `α ^ p ^ n` which is separable over `k` (it even lies in
`k`), hence `K / k` is purely inseparable.

(blueprint: `lemma-representability-picard-functor`) -/
theorem IsSepClosed.exists_isSeparable_pow_and_isPurelyInseparable [IsSepClosed k] (p : ℕ)
    [ExpChar k p] (K : Type v) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    (∀ α : K, ∃ n : ℕ, IsSeparable k (α ^ p ^ n)) ∧ IsPurelyInseparable k K := by
  refine ⟨fun α ↦ ?_, inferInstance⟩
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k p α
  exact ⟨n, ha ▸ isSeparable_algebraMap a⟩


end KBar

section PowMem

variable (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]

/-- **Purely inseparable extensions.** A field extension `E / F` of exponential characteristic
`q` is purely inseparable if and only if every `α ∈ E` satisfies `α ^ (q ^ n) ∈ F` for some `n`.
In characteristic `0` we have `q = 1`, and this says `E = F`. This is
`isPurelyInseparable_iff_pow_mem`, stated with an explicit preimage.

The other notions of the blueprint definition are those of Mathlib: `Module.Finite F E`
(finite), `Algebra.IsAlgebraic F E` (algebraic), `Algebra.IsSeparable F E` (separable), and
`IsAlgClosure F E` (algebraic closure: `E` is algebraically closed and algebraic over `F`).

(blueprint: `def-pc-field-tower`) -/
theorem isPurelyInseparable_iff_exists_algebraMap_eq_pow :
    IsPurelyInseparable F E ↔ ∀ α : E, ∃ n : ℕ, ∃ a : F, algebraMap F E a = α ^ q ^ n :=
  isPurelyInseparable_iff_pow_mem F q


end PowMem

section SeparableClosure

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Normal F E]

/-- In a normal extension `E / F`, restriction to the separable closure `F^sep` of `F` in `E` is
a bijection `Aut(E / F) → Gal(F^sep / F)`: automorphisms of `F^sep` extend to `E` as `E / F` is
normal, and uniquely as `E / F^sep` is purely inseparable. -/
theorem separableClosure.restrictNormalHom_bijective :
    Function.Bijective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (separableClosure F E)) := by
  refine ⟨fun a b h ↦ ?_, AlgEquiv.restrictNormalHom_surjective E⟩
  have hab : (a : E →+* E).comp (algebraMap (separableClosure F E) E) =
      (b : E →+* E).comp (algebraMap (separableClosure F E) E) := by
    ext s
    simpa [AlgEquiv.restrictNormalHom_apply] using congrArg Subtype.val (AlgEquiv.congr_fun h s)
  exact AlgEquiv.ext <| RingHom.congr_fun <|
    IsPurelyInseparable.injective_comp_algebraMap (separableClosure F E) E E hab

/-- In a normal extension `E / F`, the automorphism group of `E / F` is the Galois group of the
separable closure `F^sep` of `F` in `E`, by restriction. -/
noncomputable def separableClosure.autMulEquiv :
    (E ≃ₐ[F] E) ≃* Gal(separableClosure F E / F) :=
  MulEquiv.ofBijective _ (separableClosure.restrictNormalHom_bijective F E)

@[simp]
lemma separableClosure.autMulEquiv_apply_coe (σ : E ≃ₐ[F] E) (x : separableClosure F E) :
    (separableClosure.autMulEquiv F E σ x : E) = σ x :=
  AlgEquiv.restrictNormalHom_apply _ σ x

end SeparableClosure
