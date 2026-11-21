import Langlands.BaseChange.DistinguishedPlaceEpsilonComparison
import Langlands.Global.Factors.CuspidalPairEpsilonComparisonData

/-! # Distinguished-place epsilon comparison from a family of global equations -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace Langlands.BaseChange

open Global.FunctionalEquationComparison RelativeWeilEngine LocalFactor.Archimedean RankinSelberg

universe u v uX

private def gammaValue (blocks : List GammaBlock) (z : ℂ) : ℂ :=
  ((gammaProduct blocks).denominator z)⁻¹

private theorem gammaValue_append (A B : List GammaBlock) (z : ℂ) :
    gammaValue (A ++ B) z = gammaValue A z * gammaValue B z := by
  simp [gammaValue, gammaProduct, LocalFactor.ReciprocalEntire.denominator_product, mul_comm]

private theorem prod_gammaValue {I : Type*} (X : Finset I) (A : I → List GammaBlock) :
    (fun z => ∏ i ∈ X, gammaValue (A i) z) = gammaValue (X.toList.flatMap A) := by
  funext z
  rw [← Finset.prod_map_toList]
  induction X.toList with
  | nil => simp [gammaValue, gammaProduct, LocalFactor.ReciprocalEntire.denominator_product]
  | cons i is ih => simp [gammaValue_append, ih]

/-- From a finite family of base equations and an upper equation, identify
one local epsilon monomial product. The forward and dual Euler factors match
place by place over the finite fibers of the upper-to-base map. The hypotheses
also specify the Gamma counts, the archimedean epsilon dependence, and the
positive epsilon bases at the other finite places in the exceptional set. -/
def DistinguishedPlaceComparisonFromEquationsStatement : Prop :=
  ∀ (Q : Type u) [DecidableEq Q] (R : Type v) [DecidableEq R] (I : Type uX)
    (X : Finset I) (S : Finset Q) (w : Q) (w' : R) (fiber : Q → Finset R) (under : R → Q),
    w ∈ S → (∀ x v, x ∈ fiber v ↔ under x = v) → fiber w = {w'} →
    ∀ (qF : Q → ℕ) (qE : R → ℕ), (∀ v, 0 < qF v) → (∀ x, 0 < qE x) →
    ∀ (bF : I → Q → ℂˣ × ℤ) (bE : R → ℂˣ × ℤ)
      (lF ldF : I → Q → ℂ → ℂ) (lE ldE : R → ℂ → ℂ)
      (AF AdF : I → List GammaBlock) (AE AdE : List GammaBlock)
      (εF : I → ℂ → ℂ) (εE : ℂ → ℂ),
      (∀ i ∈ X, HasGlobalEquation (lF i) (ldF i)
        (fun v => epsilonMonomial (qF v) (bF i v).1 (bF i v).2)
        (gammaValue (AF i)) (gammaValue (AdF i)) (εF i) S) →
      HasGlobalEquation lE ldE (fun x => epsilonMonomial (qE x) (bE x).1 (bE x).2)
        (gammaValue AE) (gammaValue AdE) εE (S.biUnion fiber) →
      (∀ v z, (∏ i ∈ X, lF i v z) = ∏ x ∈ fiber v, lE x z) →
      (∀ v z, (∏ i ∈ X, ldF i v z) = ∏ x ∈ fiber v, ldE x z) →
      ((X.toList.flatMap AF).flatMap GammaBlock.realShifts).length =
        (AE.flatMap GammaBlock.realShifts).length →
      ((X.toList.flatMap AdF).flatMap GammaBlock.realShifts).length =
        (AdE.flatMap GammaBlock.realShifts).length →
      (∃ c : ℂˣ, ∀ z, (∏ i ∈ X, εF i z) = (c : ℂ) * εE z ∧ εE z ≠ 0) →
      (∀ v ∈ S.erase w,
        finiteEpsilonBase X (fun _ => qF v) (fun i => bF i v) =
          finiteEpsilonBase (fiber v) qE bE) →
      EpsilonMonomialProductComparison (qF w) (qE w') X (fun i => bF i w) (bE w')

theorem distinguishedPlaceComparisonFromEquations :
    DistinguishedPlaceComparisonFromEquationsStatement.{u, v, uX} := by
  intro Q _ R _ I X S w w' fiber under hw hfib hw' qF qE hqF hqE bF bE lF ldF lE ldE
    AF AdF AE AdE εF εE hF hE hEuler hDual hGamma hDualGamma hArch haux
  have hprodF := hasGlobalEquation_finsetProd X hF
  rw [prod_gammaValue X AF, prod_gammaValue X AdF] at hprodF
  have hcommon : ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∃ p pd : ℂ,
      HasProd (fun v => ∏ i ∈ X, lF i v z) p ∧ HasProd (fun x => lE x z) p ∧
      HasProd (fun v => ∏ i ∈ X, ldF i v z) pd ∧ HasProd (fun x => ldE x z) pd := by
    obtain ⟨σ, L, Ld, -, -, heuler, -⟩ := hE
    refine ⟨σ, fun z hz => ?_⟩
    obtain ⟨⟨hL, -⟩, ⟨hLd, -⟩⟩ := heuler z hz
    refine ⟨L z, Ld z, ?_, hL, ?_, hLd⟩
    · simpa only [hEuler] using hasProd_fiberwise under fiber hfib hL
    · simpa only [hDual] using hasProd_fiberwise under fiber hfib hLd
  let base : Q → ℝ := fun v => finiteEpsilonBase X (fun _ => qF v) (fun i => bF i v)
  let lift : Q → ℝ := fun v => finiteEpsilonBase (fiber v) qE bE
  have hFbase : finiteEpsilonBase (S ×ˢ X) (qF ∘ Prod.fst) (fun a => bF a.2 a.1) =
      ∏ v ∈ S, base v := Finset.prod_product S X _
  have hdisj : (S : Set Q).PairwiseDisjoint fiber := by
    intro a _ b _ hab
    exact Finset.disjoint_left.mpr fun x ha hb => hab (((hfib x a).mp ha).symm.trans ((hfib x b).mp hb))
  have hEbase : finiteEpsilonBase (S.biUnion fiber) qE bE = ∏ v ∈ S, lift v :=
    finiteEpsilonBase_biUnion S fiber hdisj qE bE
  have hFpos : 0 < ∏ v ∈ S, base v :=
    Finset.prod_pos fun v _ => finiteEpsilonBase_pos X _ _ (fun _ _ => hqF v)
  have hEpos (v : Q) : 0 < lift v :=
    finiteEpsilonBase_pos (fiber v) _ _ (fun x _ => hqE x)
  let cF : ℂˣ := ∏ a ∈ S ×ˢ X, (bF a.2 a.1).1
  let cE : ℂˣ := ∏ x ∈ S.biUnion fiber, (bE x).1
  have heF (z : ℂ) :
      (∏ v ∈ S, ∏ i ∈ X, epsilonMonomial (qF v) (bF i v).1 (bF i v).2 z) =
        (cF : ℂ) * (((∏ v ∈ S, base v) : ℝ) : ℂ) ^ (-z) := by
    have h := prod_epsilonMonomial_eq (S ×ˢ X) (qF ∘ Prod.fst) (fun a => bF a.2 a.1)
      (fun a _ => hqF a.1) z
    rw [hFbase, Finset.prod_product] at h
    exact h
  have heE (z : ℂ) :
      (∏ x ∈ S.biUnion fiber, epsilonMonomial (qE x) (bE x).1 (bE x).2 z) =
        (cE : ℂ) * (((∏ v ∈ S, lift v) : ℝ) : ℂ) ^ (-z) := by
    simpa only [hEbase] using
      prod_epsilonMonomial_eq (S.biUnion fiber) qE bE (fun x _ => hqE x) z
  have heq := finiteEpsilonBaseComparison Q R S (S.biUnion fiber) _ _ _ _ _ _
    (X.toList.flatMap AF) AE (X.toList.flatMap AdF) AdE _ _ hprodF hE hcommon hGamma hDualGamma hArch
    _ _ hFpos (Finset.prod_pos fun v _ => hEpos v) cF cE heF heE
  exact distinguishedPlaceEpsilonComparison Q S w hw base lift haux (fun v _ => hEpos v) heq
    I X (qF w) (qE w') (hqF w) (hqE w') (fun i => bF i w) (bE w') rfl
    (by simp [lift, hw', finiteEpsilonBase])

end Langlands.BaseChange
