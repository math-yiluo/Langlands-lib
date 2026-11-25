/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic polynomials along a filtration and under the linear-algebra operations

If an endomorphism `f` of a finite free module `V` preserves a submodule `W`, then the
characteristic polynomial of `f` factors as the product of the characteristic polynomials of the
restriction of `f` to `W` and of the endomorphism induced by `f` on `V ⧸ W`. Iterating this over a
filtration with graded pieces `gr_j` gives `det (1 - T f ∣ V) = ∏_j det (1 - T f ∣ gr_j)`.  This is
the characteristic-polynomial analogue of `LinearMap.det_eq_det_mul_det`, and is stated at the
same generality; Mathlib currently has only the direct-sum case `LinearMap.charpoly_prodMap`.

Over an algebraically closed field the eigenvalue multiset of an endomorphism `f`, counted with
multiplicity, is the multiset of roots `f.charpoly.roots` of its characteristic polynomial. The
second half of the file records how that multiset behaves under the standard operations: if `f`
has eigenvalues `α₁, …, α_r` and `g` has eigenvalues `β₁, …, β_t`, then `f ⊗ g` has eigenvalues
`α_i β_j`, the `s`-th exterior power `⋀^s f` has eigenvalues `α_{i₁} ⋯ α_{i_s}` for
`i₁ < ⋯ < i_s`, and the contragredient `(f⁻¹)^∨` of an invertible `f` has eigenvalues `α_i⁻¹`.
The last one splits into the transpose-invariance of the characteristic polynomial, which is
`LinearMap.charpoly_dualMap` in `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`, and
the inversion of the roots. All three are proved by choosing a basis in which `f` (and `g`) is
upper triangular, `Module.End.exists_basis_isUpperTriangular_toMatrix`, and checking that the
induced matrix is again triangular, for a suitable order on the induced basis, with the
expected diagonal.

## Main declarations

* `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`: the characteristic polynomial of an
  endomorphism preserving a submodule is the product of those of the restriction to the submodule
  and of the induced endomorphism of the quotient.
* `LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le`: the characteristic polynomial of an
  endomorphism preserving a finite filtration is the product over its graded pieces.
* `LinearMap.charpoly_mapQ_restrict_dvd`: the characteristic polynomial on an invariant
  subquotient divides the characteristic polynomial on the whole space.
* `LinearMap.charpoly_eq_one_of_subsingleton`: the characteristic polynomial of an
  endomorphism of the zero module is `1`.
* `LinearMap.charpoly_roots_tensorProduct`: the eigenvalues of a tensor product of endomorphisms
  are the pairwise products of the eigenvalues of the factors.
* `LinearMap.charpoly_roots_exteriorPower`: the eigenvalues of the `s`-th exterior power of an
  endomorphism are the products over the `s`-element sub-multisets of its eigenvalues.
* `LinearMap.charpoly_roots_dualMap_symm`: the eigenvalues of the contragredient of a linear
  automorphism are the inverses of its eigenvalues.

## Blueprint

`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`,
`LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le` and `LinearMap.charpoly_mapQ_restrict_dvd`
implement `lemma-filtrations-spectra--2`;
`LinearMap.charpoly_roots_tensorProduct`, `LinearMap.charpoly_roots_exteriorPower` and
`LinearMap.charpoly_roots_dualMap_symm` implement `lemma-filtrations-spectra`.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V]

/-- If an endomorphism preserves a submodule `W` with `W` and `V ⧸ W` finite free, its
characteristic polynomial is the product of the characteristic polynomials of the induced
endomorphisms of `W` and of `V ⧸ W`.
(blueprint: `lemma-filtrations-spectra--2`) -/
theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f : V →ₗ[R] V) (W : Submodule R V)
    [Module.Free R W] [Module.Finite R W] [Module.Free R (V ⧸ W)] [Module.Finite R (V ⧸ W)]
    (hW : W ≤ W.comap f) :
    f.charpoly = (f.restrict hW).charpoly * (W.mapQ W f hW).charpoly := by
  classical
  let bW := Module.Free.chooseBasis R W
  let bQ := Module.Free.chooseBasis R (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let B : Matrix (Module.Free.ChooseBasisIndex R W) (Module.Free.ChooseBasisIndex R (V ⧸ W)) R :=
    Matrix.of fun i l ↦ (b.repr (f (b (Sum.inr l)))) (Sum.inl i)
  suffices toMatrix b b f = Matrix.fromBlocks (toMatrix bW bW (f.restrict hW)) B 0
      (toMatrix bQ bQ (W.mapQ W f hW)) by
    rw [← charpoly_toMatrix f b, this, Matrix.charpoly_fromBlocks_zero₂₁, charpoly_toMatrix,
      charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, toMatrix_apply]
      apply Module.Basis.sumQuot_repr_inl_of_mem
    | inr l => simp [b, toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (f (bW k)) = 0 by simp [toMatrix_apply, b, this]
      rw [← mem_ker, Submodule.ker_mkQ]
      exact hW (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [toMatrix_apply, Module.Basis.sumQuot_repr_inr, Matrix.fromBlocks_apply₂₂, b]
      rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

/-- The characteristic polynomial of an endomorphism of the zero module is `1`. -/
theorem charpoly_eq_one_of_subsingleton [Nontrivial R] [Subsingleton V] (f : V →ₗ[R] V) :
    f.charpoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
    (f.charpoly_natDegree.trans Module.finrank_zero_of_subsingleton)

/-- Endomorphisms intertwined by a linear equivalence have the same characteristic
polynomial. -/
theorem charpoly_eq_of_comp_eq {V' : Type*} [AddCommGroup V'] [Module R V'] [Module.Free R V']
    [Module.Finite R V'] (e : V ≃ₗ[R] V')
    {f : V →ₗ[R] V} {g : V' →ₗ[R] V'} (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    f.charpoly = g.charpoly := by
  have hg : g = e.conj f := by
    ext x
    simpa [LinearEquiv.conj_apply] using (LinearMap.congr_fun h (e.symm x)).symm
  rw [hg, LinearEquiv.charpoly_conj]

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Iterating `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` along a finite
filtration `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n = V` by `f`-stable subspaces: the characteristic
polynomial of `f` is the product of the characteristic polynomials of the endomorphisms
induced by `f` on the graded pieces `F (i + 1) ⧸ F i`.
(blueprint: `lemma-filtrations-spectra--2`) -/
theorem charpoly_eq_prod_charpoly_mapQ_of_le (f : V →ₗ[K] V) (F : ℕ → Submodule K V) (n : ℕ)
    (h0 : F 0 = ⊥) (hn : F n = ⊤) (hle : ∀ i < n, F i ≤ F (i + 1))
    (hF : ∀ i, F i ≤ (F i).comap f) :
    f.charpoly = ∏ i ∈ Finset.range n,
      (((F i).comap (F (i + 1)).subtype).mapQ ((F i).comap (F (i + 1)).subtype)
        (f.restrict (hF (i + 1))) fun _ hx ↦ hF i hx).charpoly := by
  have key : ∀ m ≤ n, (f.restrict (hF m)).charpoly = ∏ i ∈ Finset.range m,
      (((F i).comap (F (i + 1)).subtype).mapQ ((F i).comap (F (i + 1)).subtype)
        (f.restrict (hF (i + 1))) fun _ hx ↦ hF i hx).charpoly := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Subsingleton (F 0) := by rw [h0]; infer_instance
      rw [Finset.prod_range_zero, charpoly_eq_one_of_subsingleton]
    | succ m ih =>
      intro hm
      have hW : (F m).comap (F (m + 1)).subtype ≤
          ((F m).comap (F (m + 1)).subtype).comap (f.restrict (hF (m + 1))) :=
        fun _ hx ↦ hF m hx
      rw [Finset.prod_range_succ, ← ih (by omega),
        charpoly_eq_charpoly_restrict_mul_charpoly_mapQ _ _ hW]
      congr 1
      refine charpoly_eq_of_comp_eq (Submodule.comapSubtypeEquivOfLe (hle m (by omega))) ?_
      ext x
      rfl
  rw [← key n le_rfl]
  refine charpoly_eq_of_comp_eq (LinearEquiv.ofTop (F n) hn).symm ?_
  ext x
  rfl

/-- The characteristic polynomial of the endomorphism induced by `f` on an invariant
subquotient `S ⧸ U` divides the characteristic polynomial of `f`: the eigenvalues of `f` on a
subquotient occur among those on `V`, with multiplicity.
(blueprint: `lemma-filtrations-spectra--2`) -/
theorem charpoly_mapQ_restrict_dvd (f : V →ₗ[K] V) {U S : Submodule K V}
    (hU : U ≤ U.comap f) (hS : S ≤ S.comap f) :
    ((U.comap S.subtype).mapQ (U.comap S.subtype) (f.restrict hS)
      fun _ hx ↦ hU hx).charpoly ∣ f.charpoly := by
  rw [charpoly_eq_charpoly_restrict_mul_charpoly_mapQ f S hS,
    charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f.restrict hS) (U.comap S.subtype)
      fun _ hx ↦ hU hx]
  exact (dvd_mul_left _ _).mul_right _


end Field

section IsAlgClosed

variable {K V W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The eigenvalues of the tensor product of two endomorphisms are the pairwise products of their
eigenvalues, with multiplicity.
(blueprint: `lemma-filtrations-spectra`) -/
theorem charpoly_roots_tensorProduct (f : V →ₗ[K] V) (g : W →ₗ[K] W) :
    (TensorProduct.map f g).charpoly.roots =
      (f.charpoly.roots ×ˢ g.charpoly.roots).map fun p ↦ p.1 * p.2 := by
  classical
  obtain ⟨b, hb⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix f
  obtain ⟨c, hc⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix g
  -- In the lexicographically ordered tensor basis the Kronecker product is upper triangular.
  have hbc : (toMatrix (b.tensorProduct c) (b.tensorProduct c)
      (TensorProduct.map f g)).BlockTriangular toLex := by
    rw [TensorProduct.toMatrix_map]
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    rw [Matrix.kroneckerMap_apply]
    rcases Prod.Lex.toLex_lt_toLex.mp h with h | ⟨rfl, h⟩
    · rw [hb h, zero_mul]
    · rw [hc h, mul_zero]
  rw [← charpoly_toMatrix _ (b.tensorProduct c), hbc.charpoly_roots_of_injective toLex.injective,
    ← charpoly_toMatrix f b, ← charpoly_toMatrix g c, hb.charpoly_roots_of_injective
    Function.injective_id, hc.charpoly_roots_of_injective Function.injective_id,
    TensorProduct.toMatrix_map, ← Finset.univ_product_univ, Finset.product_val]
  have key : ∀ (s : Multiset (Fin (Module.finrank K V)))
      (t : Multiset (Fin (Module.finrank K W))),
      (s ×ˢ t).map (fun p ↦ toMatrix b b f p.1 p.1 * toMatrix c c g p.2 p.2) =
        ((s.map fun i ↦ toMatrix b b f i i) ×ˢ (t.map fun i ↦ toMatrix c c g i i)).map
          fun p ↦ p.1 * p.2 := by
    intro s t
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [Multiset.cons_product, ih, Multiset.map_map]
  exact key _ _

/-- The eigenvalues of the `s`-th exterior power of an endomorphism are the products of the
`s`-element sub-multisets of its eigenvalues.
(blueprint: `lemma-filtrations-spectra`) -/
theorem charpoly_roots_exteriorPower (f : V →ₗ[K] V) (s : ℕ) :
    (exteriorPower.map s f).charpoly.roots =
      (f.charpoly.roots.powersetCard s).map Multiset.prod := by
  classical
  obtain ⟨b, hb⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix f
  set A := toMatrix b b f
  set E := toMatrix (b.exteriorPower s) (b.exteriorPower s) (exteriorPower.map s f)
  let e : Set.powersetCard (Fin (Module.finrank K V)) s → (Fin s ↪o Fin (Module.finrank K V)) :=
    fun I ↦ Set.powersetCard.ofFinEmbEquiv.symm I
  -- The entry of `⋀^s f` at `(I, J)` in the exterior basis is the minor of `A` on `I × J`.
  have hE : ∀ I J, E I J = (Matrix.of fun i j ↦ A (e I j) (e J i)).det := by
    intro I J
    rw [show E I J = _ from toMatrix_apply _ _ _ _ _, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family,
      exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMultiDual_apply_ιMulti]
    simp [A, e, toMatrix_apply]
  -- A nonzero minor needs `I` to lie termwise below `J`, so `E` is upper triangular for the
  -- order comparing first the sums of the indices and then the colexicographic order.
  let key : Set.powersetCard (Fin (Module.finrank K V)) s →
      ℕ ×ₗ Colex (Finset (Fin (Module.finrank K V))) :=
    fun I ↦ toLex (∑ i, (e I i : ℕ), toColex I.val)
  have hkey : Function.Injective key := by
    intro I J h
    simp only [key, toLex_inj, Prod.mk.injEq, toColex_inj] at h
    exact Subtype.ext h.2
  have hsum : ∀ I J, E I J ≠ 0 → ∑ i, (e I i : ℕ) ≤ ∑ i, (e J i : ℕ) ∧
      (∑ i, (e I i : ℕ) = ∑ i, (e J i : ℕ) → I = J) := by
    intro I J h
    rw [hE, Matrix.det_apply] at h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hle : ∀ i, (e I i : ℕ) ≤ e J (σ i) := by
      intro i
      by_contra! hlt
      apply hσ
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Matrix.of_apply]; exact hb (Fin.lt_def.mpr hlt)), smul_zero]
    have hσsum : ∑ i, (e J (σ i) : ℕ) = ∑ i, (e J i : ℕ) :=
      Equiv.sum_comp σ fun i ↦ (e J i : ℕ)
    refine ⟨hσsum ▸ Finset.sum_le_sum fun i _ ↦ hle i, fun heq ↦ ?_⟩
    rw [← hσsum] at heq
    have hall := (Finset.sum_eq_sum_iff_of_le fun i _ ↦ hle i).mp heq
    rw [Set.powersetCard.eq_iff_subset]
    intro x hx
    obtain ⟨i, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I x).mpr hx
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J _).mp
      ⟨σ i, (Fin.ext (hall i (Finset.mem_univ _))).symm⟩
  have htri : E.BlockTriangular key := by
    intro I J hJI
    by_contra h
    obtain ⟨hle, heq⟩ := hsum I J h
    rcases Prod.Lex.toLex_lt_toLex.mp hJI with hlt | ⟨hs, hc⟩
    · exact absurd hle (not_le.mpr hlt)
    · rw [heq hs.symm] at hc
      exact lt_irrefl _ hc
  -- A principal minor of a triangular matrix is the product of its diagonal entries.
  have hdiag : ∀ I, E I I = ∏ i, A (e I i) (e I i) := by
    intro I
    rw [hE, ← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
    · rfl
    · intro i j hij
      exact hb ((e I).strictMono hij)
  have hprod : ∀ I : Set.powersetCard (Fin (Module.finrank K V)) s,
      ∏ i, A (e I i) (e I i) = ∏ x ∈ I.val, A x x := by
    intro I
    rw [← Finset.map_orderEmbOfFin_univ I.val I.prop, Finset.prod_map]
    rfl
  have huniv :
      (Finset.univ : Finset (Set.powersetCard (Fin (Module.finrank K V)) s)).val.map Subtype.val =
      (Finset.powersetCard s (Finset.univ : Finset (Fin (Module.finrank K V)))).val := by
    refine (Multiset.Nodup.ext (Finset.univ.nodup.map Subtype.val_injective)
      (Finset.nodup _)).mpr fun x ↦ ?_
    simp [Set.powersetCard.mem_iff]
  rw [← charpoly_toMatrix _ (b.exteriorPower s), htri.charpoly_roots_of_injective hkey,
    ← charpoly_toMatrix f b, hb.charpoly_roots_of_injective Function.injective_id,
    Multiset.powersetCard_map, Multiset.map_map, ← Finset.map_val_val_powersetCard,
    Multiset.map_map, ← huniv, Multiset.map_map]
  simp_rw [hdiag, hprod]
  rfl

/-- The eigenvalues of the contragredient of a linear automorphism, that is the dual of its
inverse, are the inverses of its eigenvalues.
(blueprint: `lemma-filtrations-spectra`) -/
theorem charpoly_roots_dualMap_symm (f : V ≃ₗ[K] V) :
    (f.symm : V →ₗ[K] V).dualMap.charpoly.roots =
      (f : V →ₗ[K] V).charpoly.roots.map fun a ↦ a⁻¹ := by
  classical
  rw [charpoly_dualMap]
  obtain ⟨b, hb⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix (f : V →ₗ[K] V)
  set A := toMatrix b b f
  set A' := toMatrix b b (f.symm : V →ₗ[K] V)
  -- The matrix of `f⁻¹` is the inverse of `A`, again upper triangular, with diagonal `A i i⁻¹`.
  have h1 : A' * A = 1 := by
    rw [← toMatrix_comp, ← toMatrix_id b]
    congr 1
    ext x
    simp
  have := invertibleOfLeftInverse A A' h1
  have hA' : A'.IsUpperTriangular := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdiag : ∀ i, A' i i * A i i = 1 := by
    intro i
    have := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at this
    · exact this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA' h, zero_mul]
      · rw [hb h, mul_zero]
    · simp
  rw [← charpoly_toMatrix _ b, ← charpoly_toMatrix (f : V →ₗ[K] V) b,
    hA'.charpoly_roots_of_injective Function.injective_id,
    hb.charpoly_roots_of_injective Function.injective_id, Multiset.map_map]
  congr 1
  funext i
  exact eq_inv_of_mul_eq_one_left (hdiag i)


end IsAlgClosed

end LinearMap
