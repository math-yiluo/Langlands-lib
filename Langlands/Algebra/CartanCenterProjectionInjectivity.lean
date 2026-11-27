import Langlands.Algebra.EnvelopingPBWSymbol
import Langlands.Algebra.InvariantPolynomialRestriction

/-! # Injectivity of Cartan center projection from root-basis data -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

open Finsupp MvPolynomial

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] {r : ℕ}

/-- A central element with all Cartan PBW coordinates zero vanishes when the
root directions have transverse Cartan brackets. The function `w` is zero
on Cartan directions and one on root directions. -/
def CartanCenterProjectionInjectivityStatement (b : Module.Basis (Fin r) k L)
    (w : Fin r → ℕ) : Prop :=
  (∀ i, w i ≤ 1) →
    (∀ i, w i = 1 → ∃ x : L,
      weightedHomogeneousComponent w 0 (pbwLinearPolynomial b ⁅x, b i⁆) ≠ 0 ∧
      ∀ j, w j = 1 → j ≠ i →
        weightedHomogeneousComponent w 0 (pbwLinearPolynomial b ⁅x, b j⁆) = 0) →
    ∀ z ∈ Subalgebra.center k (UniversalEnvelopingAlgebra k L),
      (∀ a : Fin r →₀ ℕ, weight w a = 0 → (pbwMonomialBasis b).repr z a = 0) → z = 0

theorem cartanCenterProjectionInjectivity (b : Module.Basis (Fin r) k L) (w : Fin r → ℕ) :
    CartanCenterProjectionInjectivityStatement b w := by
  classical
  intro hw hBracket z hz hCartan
  by_contra hNonzero
  let coeffs := (pbwMonomialBasis b).repr z
  have hNonempty : coeffs.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hNonzero ((pbwMonomialBasis b).repr.injective (h.trans (map_zero _).symm))
  let degree := coeffs.support.sup Finsupp.degree
  obtain ⟨topIndex, htop, hDegree⟩ :=
    Finset.exists_mem_eq_sup _ hNonempty Finsupp.degree
  have hFiltration : z ∈ degreeFiltration k L degree := by
    rw [← (pbwMonomialBasis b).linearCombination_repr z, Finsupp.linearCombination_apply,
      Finsupp.sum]
    refine Submodule.sum_mem _ fun index hindex => Submodule.smul_mem _ _ ?_
    rw [pbwMonomialBasis_apply]
    apply degreeFiltration_mono k L (Finset.le_sup hindex)
    exact Langlands.Archimedean.Kostant.orderedMonomial_mem_degreeFiltration k L b
      (List.nodup_ofFn.mpr Function.injective_id) (fun i => List.mem_ofFn.mpr ⟨i, rfl⟩) index
  let p := pbwSymbol b degree z
  have hRestriction : weightedHomogeneousComponent w 0 p = 0 := by
    apply MvPolynomial.ext
    intro a
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with ha
    · change (pbwSymbol b degree z).coeff a = _
      simp [pbwSymbol_coeff, hCartan a ha]
    · simp
  have hZero : p = 0 := by
    apply InvariantPolynomialRestriction.invariantPolynomialRestriction w hw p hRestriction
    intro i hi
    obtain ⟨x, hxNonzero, hxOff⟩ := hBracket i hi
    let a := weightedHomogeneousComponent w 0 (pbwLinearPolynomial b ⁅x, b i⁆)
    refine ⟨pbwCoadjointDerivation b x, a, hxNonzero,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_, ?_⟩
    · change pbwCoadjointDerivation b x (pbwSymbol b degree z) = 0
      rw [← pbwSymbol_commutator b x hFiltration,
        (Subalgebra.mem_center_iff.mp hz (UniversalEnvelopingAlgebra.ι k x)),
        sub_self, map_zero]
    · intro index hindex
      rw [pbwCoadjointDerivation_X]
      by_cases hi' : index = i
      · subst index
        rw [ite_eq_left rfl]
      · rw [ite_eq_right hi', hxOff index hindex hi']
  have hTopCoeff := congrArg (fun p : MvPolynomial (Fin r) k => p.coeff topIndex) hZero
  change (pbwSymbol b degree z).coeff topIndex = _ at hTopCoeff
  have hTopDegree : topIndex.degree = degree := hDegree.symm
  rw [pbwSymbol_coeff, ite_eq_left hTopDegree] at hTopCoeff
  exact (Finsupp.mem_support_iff.mp htop) (by simpa using hTopCoeff)

end Langlands.Algebra.UniversalEnveloping
