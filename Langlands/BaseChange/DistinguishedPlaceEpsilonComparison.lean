import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction
import Langlands.Global.Factors.FiniteEpsilonBaseComparison

/-! # Isolation of the distinguished finite epsilon comparison -/

noncomputable section

open scoped BigOperators

namespace Langlands.Global.FunctionalEquationComparison

/-- Regroup the positive bases over disjoint fibers of finite places. -/
theorem finiteEpsilonBase_biUnion {Q R : Type*} [DecidableEq R] (S : Finset Q)
    (fiber : Q → Finset R) (hdisj : (S : Set Q).PairwiseDisjoint fiber)
    (q : R → ℕ) (e : R → ℂˣ × ℤ) :
    finiteEpsilonBase (S.biUnion fiber) q e = ∏ v ∈ S, finiteEpsilonBase (fiber v) q e :=
  Finset.prod_biUnion hdisj

end Langlands.Global.FunctionalEquationComparison

namespace Langlands.BaseChange

open Global.FunctionalEquationComparison RankinSelberg

universe u v

/-- At the distinguished place, equality of the global finite epsilon bases
and the auxiliary-place comparisons give the local monomial comparison used
by the cuspidal conductor reduction. The base products are supplied after
regrouping the finite places. -/
def DistinguishedPlaceEpsilonComparisonStatement : Prop :=
  ∀ (Place : Type u) [DecidableEq Place] (S : Finset Place) (w : Place), w ∈ S →
    ∀ (base lift : Place → ℝ),
      (∀ v ∈ S.erase w, base v = lift v) → (∀ v ∈ S.erase w, 0 < lift v) →
      (∏ v ∈ S, base v) = (∏ v ∈ S, lift v) →
    ∀ (ι : Type v) (X : Finset ι) (qF qE : ℕ), 0 < qF → 0 < qE →
    ∀ (eF : ι → ℂˣ × ℤ) (eE : ℂˣ × ℤ),
      base w = finiteEpsilonBase X (fun _ => qF) eF →
      lift w = (qE : ℝ) ^ eE.2 →
      EpsilonMonomialProductComparison qF qE X eF eE

theorem distinguishedPlaceEpsilonComparison : DistinguishedPlaceEpsilonComparisonStatement.{u, v} := by
  intro Place _ S w hw base lift haux hpos hprod ι X qF qE hqF hqE eF eE hbase hlift
  have hrest : (∏ v ∈ S.erase w, base v) = ∏ v ∈ S.erase w, lift v :=
    Finset.prod_congr rfl haux
  rw [← Finset.mul_prod_erase S base hw, ← Finset.mul_prod_erase S lift hw, hrest] at hprod
  have hpoint := mul_right_cancel₀ (Finset.prod_pos hpos).ne' hprod
  rw [hbase, hlift] at hpoint
  refine ⟨(∏ i ∈ X, (eF i).1) / eE.1, fun z => ?_⟩
  have hE : epsilonMonomial qE eE.1 eE.2 z = (eE.1 : ℂ) *
      (((qE : ℝ) ^ eE.2 : ℝ) : ℂ) ^ (-z) := by
    simpa only [Finset.prod_singleton, finiteEpsilonBase] using
      (prod_epsilonMonomial_eq ({()} : Finset Unit) (fun _ => qE) (fun _ => eE)
        (fun _ _ => hqE) z)
  rw [prod_epsilonMonomial_eq X _ _ (fun _ _ => hqF), hpoint, hE,
    Units.val_div_eq_div_val]
  field_simp [eE.1.ne_zero]

end Langlands.BaseChange
