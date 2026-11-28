import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.Algebra.CentralSimple.LandherrQuadraticData
import Langlands.FieldTheory.RealAlgebraicClosure
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-! # Unitary splitting at archimedean completions -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open NumberField

universe u

/-- If every quadratic extension of `K` is algebraically closed, then `K` has the unitary
splitting property: central simple algebras over algebraically closed fields are split. -/
theorem unitaryInvolutionSplitting_of_isAlgClosed (K : Type u) [Field K]
    (h : ∀ (L : Type u) [Field L] [Algebra K L], Algebra.IsQuadraticExtension K L →
      IsAlgClosed L) :
    UnitaryInvolutionSplitting K := by
  intro L _ _ hq _ σ _ B' _ _ _ _ _ τ' _
  have := h L hq
  obtain ⟨n, _, ⟨e⟩⟩ := exists_matrix_chart L B' L
  exact ⟨n, ⟨(Algebra.TensorProduct.lid L B').symm.trans e⟩⟩

/-- A quadratic extension of a field isomorphic to `ℝ` is algebraically closed. -/
theorem isAlgClosed_of_quadratic_of_equiv_real {K : Type u} [Field K] (e : K ≃+* ℝ)
    (L : Type u) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] : IsAlgClosed L := by
  have : FiniteDimensional K L :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]; decide)
  have hd : Module.finrank K (AlgebraicClosure K) = 2 :=
    FieldTheory.finrank_algebraicClosure_of_equiv_real e
  have : FiniteDimensional K (AlgebraicClosure K) := .of_finrank_pos (by rw [hd]; decide)
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have hbij : Function.Bijective f := by
    refine ⟨f.injective, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L, hd])).mp f.injective
  exact IsAlgClosed.of_ringEquiv (AlgebraicClosure K) L (AlgEquiv.ofBijective f hbij).symm.toRingEquiv

/-- An algebraically closed field has no quadratic extension. -/
theorem not_isQuadratic_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    (L : Type u) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] : False := by
  have : FiniteDimensional K L :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]; decide)
  obtain ⟨x, hx⟩ := exists_not_mem_range K L
  exact hx ((IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := L)).2 x)

/-- Every archimedean completion of a number field has the unitary splitting property. -/
theorem infiniteCompletion_unitaryInvolutionSplitting {F : Type u} [Field F] [NumberField F]
    (v : InfinitePlace F) : UnitaryInvolutionSplitting v.Completion := by
  apply unitaryInvolutionSplitting_of_isAlgClosed
  intro L _ _ hq
  rcases v.isReal_or_isComplex with hv | hv
  · exact isAlgClosed_of_quadratic_of_equiv_real (InfinitePlace.Completion.ringEquivRealOfIsReal hv) L
  · have : IsAlgClosed v.Completion := by
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      apply IsAlgClosed.of_exists_root
      intro p _ hp
      have hdeg : (p.map e.toRingHom).degree ≠ 0 := by
        rw [Polynomial.degree_map]
        exact (Polynomial.degree_pos_of_irreducible hp).ne'
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map e.toRingHom) hdeg
      refine ⟨e.symm z, ?_⟩
      have key : Polynomial.eval (e.symm z) p =
          e.symm.toRingHom (Polynomial.eval z (p.map e.toRingHom)) := by
        rw [Polynomial.eval_map, Polynomial.hom_eval₂]
        have hc : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by ext x; simp
        rw [hc]
        rfl
      rw [key, hz.eq_zero, map_zero]
    exact (not_isQuadratic_of_isAlgClosed (K := v.Completion) L).elim

end Langlands.CentralSimple.Landherr
