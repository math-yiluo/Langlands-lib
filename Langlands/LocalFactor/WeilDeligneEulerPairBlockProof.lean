import Langlands.LocalFactor.WeilDeligneEulerStatement
import Langlands.LocalFactor.WeilDeligneBlockPair
import Langlands.LocalFactor.UnramifiedDegree

/-! # The ordinary pair-block Euler statement -/

noncomputable section

universe uK uG uV uW

open scoped BigOperators

namespace Langlands.LocalFactor

/-- The published block-kernel computation proves all three ordinary formulas. -/
theorem wdEulerPairBlock : WDEulerPairBlockStatement.{uK, uG, uV, uW} := by
  intro K _ _ G _ ν I _ hν Φ A B n m
  let D := FiniteRepresentation.invariants I (FiniteRepresentation.tensor A B)
  let P := WeilDeligneRepresentation.tensor
    (WeilDeligneRepresentation.block ν A (n + 1))
    (WeilDeligneRepresentation.block ν B (m + 1))
  let J := WeilDeligneRepresentation.inertiaKernelRepresentation I P
  have hpoly : eulerPolynomial (J.representation Φ) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (n + m - j.val) • D.representation Φ) := by
    change WeilDeligne.eulerPolynomial P I Φ = _
    rw [WeilDeligne.eulerPolynomial_block_block ν A B n m I hν Φ,
      WeilDeligne.blockPairKernelOperator, eulerPolynomial_pi]
    rfl
  have hidentity : WeilDeligne.blockPairKernelOperator ν A B n m I 1 =
      (1 : Module.End K (Fin (min (n + 1) (m + 1)) →
        ↥(Representation.invariants ((A.representation.tprod B.representation).comp I.subtype)))) := by
    apply LinearMap.ext
    intro x
    funext j
    change (ν 1 : K) ^ (n + m - j.val) • D.representation 1 (x j) = x j
    simp only [map_one, Units.val_one, one_pow, one_smul]
    rfl
  have hr := congrArg Polynomial.natDegree
    (WeilDeligne.eulerPolynomial_block_block ν A B n m I hν 1)
  change (eulerPolynomial (J.representation 1)).natDegree =
    (eulerPolynomial (WeilDeligne.blockPairKernelOperator ν A B n m I 1)).natDegree at hr
  rw [hidentity, eulerPolynomial_natDegree_representation] at hr
  have hidDegree := eulerPolynomial_natDegree_of_isUnit
    (1 : Module.End K (Fin (min (n + 1) (m + 1)) →
      ↥(Representation.invariants ((A.representation.tprod B.representation).comp I.subtype))))
    isUnit_one
  have hrDimension := hr.trans hidDegree
  have hrank : J.rank = min (n + 1) (m + 1) * D.rank := by
    change J.rank = min (n + 1) (m + 1) * Module.finrank K
      ↥(Representation.invariants ((A.representation.tprod B.representation).comp I.subtype))
    simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, FiniteRepresentation.rank] using hrDimension
  change eulerPolynomial (J.representation Φ) =
      (∏ j : Fin (min (n + 1) (m + 1)),
        eulerPolynomial ((ν Φ : K) ^ (n + m - j.val) • D.representation Φ)) ∧
    rationalFactor (J.representation Φ) =
      (∏ j : Fin (min (n + 1) (m + 1)),
        rationalFactor ((ν Φ : K) ^ (n + m - j.val) • D.representation Φ)) ∧
    J.rank = min (n + 1) (m + 1) * D.rank
  refine ⟨hpoly, ?_, hrank⟩
  simp only [rationalFactor, hpoly, map_prod, Finset.prod_inv_distrib]

end Langlands.LocalFactor
