import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.BaseChange.DistinguishedEulerPolynomialVanishing
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Euler comparison at the single distinguished upper completion -/

noncomputable section

set_option autoImplicit false

universe u uQ uX

open scoped BigOperators NumberField

namespace Langlands.BaseChange

open Global Automorphic LocalFactor.Archimedean _root_.Polynomial RankinSelberg
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison RelativeWeilEngine

private theorem prod_gamma_denominator_inv {I : Type*} (X : Finset I) (A : I → List GammaBlock) :
    (fun z => ∏ i ∈ X, ((gammaProduct (A i)).denominator z)⁻¹) =
      fun z => ((gammaProduct (X.toList.flatMap A)).denominator z)⁻¹ := by
  have happ (B C : List GammaBlock) (z : ℂ) :
      ((gammaProduct (B ++ C)).denominator z)⁻¹ =
        ((gammaProduct B).denominator z)⁻¹ * ((gammaProduct C).denominator z)⁻¹ := by
    simp [gammaProduct, LocalFactor.ReciprocalEntire.denominator_product, mul_comm]
  funext z
  rw [← Finset.prod_map_toList]
  induction X.toList with
  | nil => simp [gammaProduct, LocalFactor.ReciprocalEntire.denominator_product]
  | cons i is ih => simp [happ, ih]

private theorem continuous_epsilonMonomial {q : ℕ} (hq : 1 < q) (c : ℂˣ) (m : ℤ) :
    Continuous (epsilonMonomial q c m) := by
  have hs : Continuous (spectralPoint q) := by
    simpa only [eval_X] using
      (Global.CuspidalPairBoundaryNonvanishing.differentiable_eval_spectralPoint X
        (Nat.zero_lt_one.trans hq)).continuous
  exact continuous_const.mul (hs.zpow₀ m fun z => Or.inl (spectralPoint_ne_zero hq z))

private theorem hasProd_mul_distinguished {Q R : Type*} [DecidableEq Q]
    (under : R → Q) (fiber : Q → Finset R) (hfib : ∀ w v, w ∈ fiber v ↔ under w = v)
    (v₀ : Q) (w₀ : R) (hw₀ : fiber v₀ = {w₀}) (l : Q → ℂ) (l' : R → ℂ)
    (a p : ℂ) (hprod : HasProd l' p) (hp : p ≠ 0) (hl : l v₀ = 1) (hl' : l' w₀ = a⁻¹)
    (haway : ∀ v ≠ v₀, l v = ∏ w ∈ fiber v, l' w) : HasProd l (a * p) := by
  have ha : a ≠ 0 := by
    intro h
    exact ne_zero_of_hasProd hprod hp w₀ (by simp [hl', h])
  apply ((hasProd_pi_single v₀ a).mul (hasProd_fiberwise under fiber hfib hprod)).congr_fun
  intro v
  by_cases hv : v = v₀
  · subst v
    simp [hw₀, hl, hl', ha]
  · simp [Pi.mulSingle, Function.update_of_ne hv, haway v hv]

/-- Completed pair equations and the local Euler matches away from `v₀` force the
upper Euler polynomials at the unique `w₀` to be one when the lower factors are
one and the upper forward and reflected dual polynomials have disjoint roots. -/
def CompletedPairDistinguishedEulerComparisonStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (r t : ℕ) (I : Type uX) [Fintype I],
    ∀ (v₀ : FinitePlace K) (w₀ : FinitePlace L), placesAbove L v₀ = {w₀} →
    ∀ (T Td : I → CuspidalOperatorRealization K r) (T' Td' : I → CuspidalOperatorRealization K t)
      (U Ud : CuspidalOperatorRealization L r) (U' Ud' : CuspidalOperatorRealization L t)
      (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
      (P' : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T' i))
      (Pd : ∀ i, CuspidalSpectralPresentation.{u, uQ} (Td i))
      (Pd' : ∀ i, CuspidalSpectralPresentation.{u, uQ} (Td' i))
      (Q : CuspidalSpectralPresentation.{u, uQ} U) (Q' : CuspidalSpectralPresentation.{u, uQ} U')
      (Qd : CuspidalSpectralPresentation.{u, uQ} Ud) (Qd' : CuspidalSpectralPresentation.{u, uQ} Ud')
      (hP : ∀ i, HasIrreducibleAdmissibleComponents (P i))
      (hP' : ∀ i, HasIrreducibleAdmissibleComponents (P' i))
      (hPd : ∀ i, HasIrreducibleAdmissibleComponents (Pd i))
      (hPd' : ∀ i, HasIrreducibleAdmissibleComponents (Pd' i))
      (hQ : HasIrreducibleAdmissibleComponents Q) (hQ' : HasIrreducibleAdmissibleComponents Q')
      (hQd : HasIrreducibleAdmissibleComponents Qd) (hQd' : HasIrreducibleAdmissibleComponents Qd')
      (cF : ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K) (P i) (P' i) (Pd i) (Pd' i)
        (hP i) (hP' i) (hPd i) (hPd' i))
      (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L) Q Q' Qd Qd' hQ hQ' hQd hQd')
      (SF : I → Finset (FinitePlace K)) (SE : Finset (FinitePlace L))
      (AF AdF : I → List GammaBlock) (AE AdE : List GammaBlock) (εF : I → ℂˣ) (εE : ℂˣ),
      (∀ i v, v ∉ SF i → (cF i).epsilon v = (1, 0)) →
      (∀ i, HasGlobalEquation (cF i).finiteL (cF i).finiteDualL (cF i).finiteEpsilon
        (fun z => ((gammaProduct (AF i)).denominator z)⁻¹)
        (fun z => ((gammaProduct (AdF i)).denominator z)⁻¹) (fun _ => (εF i : ℂ)) (SF i)) →
      HasGlobalEquation cE.finiteL cE.finiteDualL cE.finiteEpsilon
        (fun z => ((gammaProduct AE).denominator z)⁻¹)
        (fun z => ((gammaProduct AdE).denominator z)⁻¹) (fun _ => (εE : ℂ)) SE →
      (∀ i, (cF i).lPolynomial v₀ = 1 ∧ (cF i).dualLPolynomial v₀ = 1) →
      (∀ v ≠ v₀, ∀ z, (∏ i, (cF i).finiteL v z) = ∏ w ∈ placesAbove L v, cE.finiteL w z) →
      (∀ v ≠ v₀, ∀ z, (∏ i, (cF i).finiteDualL v z) = ∏ w ∈ placesAbove L v, cE.finiteDualL w z) →
      (∀ x : ℂ, x ≠ 0 → (cE.lPolynomial w₀).eval x = 0 →
        (cE.dualLPolynomial w₀).eval ((residueCardinality w₀ : ℂ)⁻¹ / x) ≠ 0) →
      cE.lPolynomial w₀ = 1 ∧ cE.dualLPolynomial w₀ = 1

set_option maxHeartbeats 1800000 in
/-- Combine the lower equations and compare their Euler products with the upper
products after removing the distinguished polynomial denominator from each. -/
theorem completedPairDistinguishedEulerComparison :
    CompletedPairDistinguishedEulerComparisonStatement.{u, uQ, uX} := by
  classical
  intro K L _ _ _ _ _ _ _ r t I _ v₀ w₀ hw T Td T' Td' U Ud U' Ud' P P' Pd Pd' Q Q' Qd Qd'
    hP hP' hPd hPd' hQ hQ' hQd hQd' cF cE SF SE AF AdF AE AdE εF εE hSF hF hE h₀ haway hdaway hsep
  let S := Finset.univ.biUnion SF
  have hsub (i : I) : SF i ⊆ S := fun _ h => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩
  have hF' (i : I) := (hF i).changeSet (T' := S) (fun v hv hn => False.elim (hn (hsub i hv)))
    (fun v _ hn z => by simp [FinitePairFactorChoice.finiteEpsilon, hSF i v hn])
  have hprodF := hasGlobalEquation_finsetProd Finset.univ (fun i _ => hF' i)
  rw [prod_gamma_denominator_inv, prod_gamma_denominator_inv] at hprodF
  have hqF (v : FinitePlace K) := FinitePairFactorChoice.one_lt_residueCardinality v
  have hqE (w : FinitePlace L) := FinitePairFactorChoice.one_lt_residueCardinality w
  have hcontF (i : I) (v : FinitePlace K) : Continuous ((cF i).finiteEpsilon v) :=
    continuous_epsilonMonomial (hqF v) _ _
  have hcontE (w : FinitePlace L) : Continuous (cE.finiteEpsilon w) :=
    continuous_epsilonMonomial (hqE w) _ _
  have hneF (i : I) (v : FinitePlace K) (z : ℂ) : (cF i).finiteEpsilon v z ≠ 0 :=
    epsilonMonomial_ne_zero _ (by exact_mod_cast (Nat.zero_lt_one.trans (hqF v))) _ _ _
  have hneE (w : FinitePlace L) (z : ℂ) : cE.finiteEpsilon w z ≠ 0 :=
    epsilonMonomial_ne_zero _ (by exact_mod_cast (Nat.zero_lt_one.trans (hqE w))) _ _ _
  refine distinguishedEulerFromEquations (FinitePlace K) (FinitePlace L) S SE _ _ _ _ _ _
    (Finset.univ.toList.flatMap AF) (Finset.univ.toList.flatMap AdF) AE AdE
    (fun _ => ∏ i, (εF i : ℂ)) (fun _ => (εE : ℂ)) (residueCardinality w₀)
    (cE.lPolynomial w₀) (cE.dualLPolynomial w₀) (hqE w₀) (cE.lPolynomial_spec w₀).coeff_zero
    (cE.dualLPolynomial_spec w₀).coeff_zero hprodF hE ?_ ?_ ?_ ?_ ?_ hsep
  · exact continuous_const.mul (continuous_finsetProd _ fun v _ =>
      continuous_finsetProd _ fun i _ => hcontF i v)
  · exact continuous_const.mul (continuous_finsetProd _ fun w _ => hcontE w)
  · intro z
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (εF i).ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun v _ => Finset.prod_ne_zero_iff.mpr fun i _ => hneF i v z)
  · intro z
    exact mul_ne_zero εE.ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => hneE w z)
  · obtain ⟨σ, U, Ud, -, -, hp, -⟩ := hE
    refine ⟨σ, fun z hz => ?_⟩
    obtain ⟨⟨hU, hUne⟩, hUd, hUdne⟩ := hp z hz
    refine ⟨U z, Ud z, ?_, hU, ?_, hUd⟩
    · exact hasProd_mul_distinguished (fun w : FinitePlace L => w.under (𝓞 K)) (placesAbove L)
        mem_placesAbove v₀ w₀ hw _ _ _ _ hU hUne
        (Finset.prod_eq_one fun i _ => by simp [FinitePairFactorChoice.finiteL, (h₀ i).1])
        rfl (fun v hv => haway v hv z)
    · exact hasProd_mul_distinguished (fun w : FinitePlace L => w.under (𝓞 K)) (placesAbove L)
        mem_placesAbove v₀ w₀ hw _ _ _ _ hUd hUdne
        (Finset.prod_eq_one fun i _ => by simp [FinitePairFactorChoice.finiteDualL, (h₀ i).2])
        rfl (fun v hv => hdaway v hv z)

end Langlands.BaseChange
