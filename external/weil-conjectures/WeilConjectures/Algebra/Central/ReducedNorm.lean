/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.JacobsonNoether
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import WeilConjectures.Mathlib.Algebra.Central.Matrix
public import WeilConjectures.Mathlib.Algebra.Central.TensorProduct
public import WeilConjectures.Mathlib.FieldTheory.Galois.Infinite
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Mathlib.RingTheory.MatrixAlgebra

/-!
# The reduced norm of a central division algebra

Let `D` be a finite-dimensional central division algebra over a field `K`. Over a separable
closure `K^sep` of `K` it becomes a matrix algebra, `K^sep ⊗[K] D ≅ M_d(K^sep)`, so
`dim_K D = d ^ 2`. The determinant of `∑ Tᵢ (1 ⊗ bᵢ)` for a `K`-basis `(bᵢ)` of `D` is a form of
degree `d` in `d ^ 2` variables, the *reduced norm*. Its coefficients are fixed by
`Gal(K^sep / K)`, since the Galois conjugate of a splitting is another splitting and the two
differ by an automorphism of `M_d(K^sep)`, which is inner. Hence the reduced norm is defined
over `K`, and it vanishes only at `0` because nonzero elements of `D` are invertible.

## Main statements

- `Algebra.IsCentral.exists_algEquiv_matrix_of_isSepClosed`: a central simple algebra splits
  over a separably closed field.
- `Algebra.IsCentral.exists_isHomogeneous_eval_ne_zero`: the reduced norm of a central division
  algebra `D` of dimension `d ^ 2` is a form of degree `d` with no nontrivial zero.
-/

@[expose] public section

open TensorProduct

namespace MvPolynomial

/-- Conjugating each matrix `N i` by the same unit `g` does not change the determinant of the
generic matrix `∑ i, X i • N i`. -/
theorem det_sum_X_smul_map_C_conj {ι σ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    [Fintype σ] (g : (Matrix ι ι R)ˣ) (N : σ → Matrix ι ι R) :
    (∑ i, (X i : MvPolynomial σ R) •
        (g * N i * g⁻¹ : Matrix ι ι R).map (C : R →+* MvPolynomial σ R)).det =
      (∑ i, (X i : MvPolynomial σ R) • (N i).map (C : R →+* MvPolynomial σ R)).det := by
  have h : ∑ i, (X i : MvPolynomial σ R) •
        (g * N i * g⁻¹ : Matrix ι ι R).map (C : R →+* MvPolynomial σ R) =
      (g : Matrix ι ι R).map C *
        (∑ i, (X i : MvPolynomial σ R) • (N i).map (C : R →+* MvPolynomial σ R)) *
        (g⁻¹ : (Matrix ι ι R)ˣ).1.map C := by
    simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul]
  rw [h, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, ← Matrix.map_mul,
    Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one, one_mul]

end MvPolynomial

namespace Algebra.IsCentral

/-- A finite-dimensional central division algebra over a separably closed field `F` is `F`
itself. -/
theorem bot_eq_top_of_isSepClosed (F E : Type*) [Field F] [IsSepClosed F] [DivisionRing E]
    [Algebra F E] [Algebra.IsCentral F E] [FiniteDimensional F E] :
    (⊥ : Subalgebra F E) = ⊤ := by
  by_contra h
  obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' h
  have hint : IsIntegral F x := hsep.isIntegral
  exact hx (Algebra.mem_bot.mpr (minpoly.mem_range_of_degree_eq_one F x
    (IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint) hsep)))

/-- **Splitting over a separably closed field.** A finite-dimensional central simple algebra `A`
over `K` becomes a matrix algebra over every separably closed field `F` containing `K`: by
Wedderburn's theorem `F ⊗[K] A ≅ M_d(E)` for a central division algebra `E` over `F`, and
`E = F` by the Jacobson–Noether theorem.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
@[stacks 03R2]
theorem exists_algEquiv_matrix_of_isSepClosed (K A F : Type*) [Field K] [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [Field F] [IsSepClosed F]
    [Algebra K F] :
    ∃ (d : ℕ) (_ : NeZero d), Nonempty (F ⊗[K] A ≃ₐ[F] Matrix (Fin d) (Fin d) F) := by
  have : IsArtinianRing (F ⊗[K] A) := IsArtinianRing.of_finite F _
  obtain ⟨d, hd, E, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F (F ⊗[K] A)
  have : Algebra.IsCentral F E := of_algEquiv_matrix e
  have hbij : Function.Bijective (Algebra.ofId F E) :=
    ⟨(algebraMap F E).injective, fun x => Algebra.mem_bot.mp
      ((bot_eq_top_of_isSepClosed F E).symm ▸ Algebra.mem_top)⟩
  exact ⟨d, hd, ⟨e.trans (AlgEquiv.ofBijective _ hbij).symm.mapMatrix⟩⟩

/-- If `φ : L ⊗[K] A ≃ₐ[L] M_ι(L)` is a splitting and `τ ∈ Gal(L / K)`, then applying `τ`
entrywise to `φ (1 ⊗ a)` is conjugation by a unit independent of `a`: the twisted splitting
`τ ∘ φ ∘ (τ⁻¹ ⊗ 1)` differs from `φ` by an automorphism of `M_ι(L)`, which is inner.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
theorem exists_unit_map_eq_conj {K L A ι : Type*} [Field K] [Field L] [Algebra K L] [Ring A]
    [Algebra K A] [Fintype ι] [DecidableEq ι] (φ : L ⊗[K] A ≃ₐ[L] Matrix ι ι L)
    (τ : L ≃ₐ[K] L) :
    ∃ g : (Matrix ι ι L)ˣ, ∀ a : A, (φ (1 ⊗ₜ a)).map τ = g * φ (1 ⊗ₜ a) * g⁻¹ := by
  let f : Matrix ι ι L ≃+* Matrix ι ι L := φ.symm.toRingEquiv.trans
    ((Algebra.TensorProduct.congr τ.symm AlgEquiv.refl).toRingEquiv.trans
      (φ.toRingEquiv.trans (τ.mapMatrix (m := ι)).toRingEquiv))
  let ψ : Matrix ι ι L ≃ₐ[L] Matrix ι ι L := AlgEquiv.ofRingEquiv (f := f) fun c => by
    simp only [f, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, Algebra.algebraMap_self_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_refl, id_eq]
    rw [← Algebra.algebraMap_self_apply (τ.symm c), ← Algebra.TensorProduct.algebraMap_apply,
      AlgEquiv.commutes]
    ext i j
    by_cases h : i = j
    · simp [Matrix.algebraMap_matrix_apply, h]
    · simp [Matrix.algebraMap_matrix_apply, h]
  obtain ⟨g, hg⟩ := Matrix.exists_unit_conj_of_algEquiv ψ
  refine ⟨g, fun a => ?_⟩
  rw [← hg]
  simp [ψ, f]

open MvPolynomial in
/-- **The reduced norm.** A finite-dimensional central division algebra `D` over `K` has
dimension `d ^ 2` for some `d > 0`, and in the coordinates of a `K`-basis of `D` there is a form
of degree `d` over `K`, the reduced norm, vanishing only at `0`.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
theorem exists_isHomogeneous_eval_ne_zero (K D : Type*) [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] :
    ∃ d : ℕ, 0 < d ∧ Module.finrank K D = d ^ 2 ∧
      ∃ P : MvPolynomial (Fin (Module.finrank K D)) K, P.IsHomogeneous d ∧
        ∀ y : Fin (Module.finrank K D) → K, y ≠ 0 → MvPolynomial.eval y P ≠ 0 := by
  classical
  let b := Module.finBasis K D
  obtain ⟨d, hd, ⟨φ⟩⟩ := exists_algEquiv_matrix_of_isSepClosed K D (SeparableClosure K)
  have hn : Module.finrank K D = d ^ 2 := by
    rw [← Module.finrank_baseChange (R := SeparableClosure K), φ.toLinearEquiv.finrank_eq,
      Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, sq]
  let M (i : Fin (Module.finrank K D)) : Matrix (Fin d) (Fin d) (SeparableClosure K) :=
    φ (1 ⊗ₜ b i)
  let G : Matrix (Fin d) (Fin d) (MvPolynomial (Fin (Module.finrank K D)) (SeparableClosure K)) :=
    ∑ i, (X i : MvPolynomial _ (SeparableClosure K)) • (M i).map C
  have hG : G.det.IsHomogeneous d := by
    have h := IsHomogeneous.det (M := G) (m := 1) fun r c => by
      simp only [G, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact IsHomogeneous.sum _ _ _ fun i _ => by
        simpa using (isHomogeneous_X _ i).mul (isHomogeneous_C _ (M i r c))
    rwa [Fintype.card_fin, mul_one] at h
  have hinv (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      map (τ : SeparableClosure K →+* SeparableClosure K) G.det = G.det := by
    obtain ⟨g, hg⟩ := exists_unit_map_eq_conj φ τ
    rw [RingHom.map_det, ← det_sum_X_smul_map_C_conj g M]
    simp only [G, M, ← hg]
    congr 1
    refine Matrix.ext fun r c => ?_
    simp [Matrix.sum_apply]
  obtain ⟨P, hP⟩ := exists_map_algebraMap_eq_of_forall_map_eq _ hinv
  refine ⟨d, Nat.pos_of_ne_zero hd.out, hn, P, ?_, fun y hy => ?_⟩
  · exact IsHomogeneous.of_map (algebraMap K _).injective (hP ▸ hG)
  · have hx : (∑ i, y i • b i) ≠ 0 := by
      rwa [← b.equivFun_symm_apply, ne_eq, LinearEquiv.map_eq_zero_iff]
    have hu := ((Ne.isUnit hx).map (Algebra.TensorProduct.includeRight (R := K)
      (A := SeparableClosure K))).map φ
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    intro h0
    apply hu.ne_zero
    have h := congrArg (algebraMap K (SeparableClosure K)) h0
    rw [map_zero, eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id, ← eval_map, hP,
      RingHom.map_det] at h
    convert h using 2
    refine Matrix.ext fun r c => ?_
    simp only [map_sum, map_smul, Algebra.TensorProduct.includeRight_apply, Matrix.sum_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, eval_X,
      Function.comp_apply, eval_C, G, M]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul (A := SeparableClosure K) (M := SeparableClosure K ⊗[K] D) (y i),
      map_smul, Matrix.smul_apply, smul_eq_mul]

end Algebra.IsCentral
