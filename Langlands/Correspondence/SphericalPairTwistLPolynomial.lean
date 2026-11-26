import Langlands.Correspondence.SphericalStandardTwistFactors
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # Pair L-polynomials of determinant twists of spherical representations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Correspondence

open GeneralLinear Unramified RankinSelberg Polynomial
open LocalFactor.PadicAbelian (lPolynomial uniformizerUnit)
open Langlands.Global.CuspidalPairFunctionalEquation (pairEulerPolynomial pairEulerPolynomial_ofTuple)

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance (n : ℕ) : TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

local notation "T" => K.canonicalTopologicalData

private theorem lPolynomial_character_mul_twist (x y : ℂˣ) (ω : QuasiCharacter K) :
    lPolynomial T (character K x * ω * character K y) =
      if (T).multiplicativeConductor ω = 0 then
        (1 - C ((x : ℂ) * (y : ℂ)) * X).comp (C (ω (T).uniformizerUnit : ℂ) * X)
      else 1 := by
  classical
  have hunit (z : ℂˣ) (a : K.Carrierˣ) (ha : (T).discreteValuation (a : K.Carrier) = 1) :
      character K z a = 1 :=
    ((T).multiplicativeConductor_eq_zero_iff (character K z)).mp
      (multiplicativeConductor_character K z) a ha
  have hc : (T).multiplicativeConductor (character K x * ω * character K y) = 0 ↔
      (T).multiplicativeConductor ω = 0 := by
    simp only [(T).multiplicativeConductor_eq_zero_iff,
      PadicField.TopologicalData.IsUnramifiedQuasicharacter]
    have he (a : K.Carrierˣ) (ha : (T).discreteValuation (a : K.Carrier) = 1) :
        ((character K x * ω * character K y) a = 1) ↔ ω a = 1 := by
      change (character K x a * ω a * character K y a = 1) ↔ ω a = 1
      rw [hunit x a ha, hunit y a ha, one_mul, mul_one]
    exact ⟨fun h a ha => (he a ha).mp (h a ha), fun h a ha => (he a ha).mpr (h a ha)⟩
  unfold lPolynomial
  rw [if_congr hc rfl rfl]
  split
  · change 1 - C ((character K x (T).uniformizerUnit * ω (T).uniformizerUnit *
        character K y (T).uniformizerUnit : ℂˣ) : ℂ) * X = _
    simp only [character_uniformizer, Units.val_mul, sub_comp, one_comp,
      mul_comp, C_comp, X_comp]
    have hmul : (x : ℂ) * (ω (T).uniformizerUnit : ℂ) * (y : ℂ) =
        ((x : ℂ) * (y : ℂ)) * (ω (T).uniformizerUnit : ℂ) := by ring
    rw [hmul, C_mul, mul_assoc]
  · rfl

/-- The pair L-polynomial of a spherical pair after a determinant twist of the
first member. An unramified twist scales the spectral variable and a ramified
one makes the polynomial one. -/
def SphericalPairTwistLPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p) {r t : ℕ}
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K),
    IsSelfDualMeasure K ψ ν →
    ∀ (A Aω : AutomorphicObject.{u,u} K r.succPNat)
      (B : AutomorphicObject.{u,u} K t.succPNat)
      (s : Eigenvalues (r + 1)) (s' : Eigenvalues (t + 1)),
      HasSphericalSpectrum K A s → HasSphericalSpectrum K B s' →
      ∀ (ω : QuasiCharacter K),
        IsCharacterTwist K ω (automorphicClassOf K A) (automorphicClassOf K Aω) →
        ∀ P : Polynomial ℂ,
          IsAutomorphicPairLPolynomial K ψ ν (automorphicClassOf K Aω)
            (automorphicClassOf K B) P →
          P = if K.canonicalTopologicalData.multiplicativeConductor ω = 0 then
            (pairEulerPolynomial s s').comp
              (C (ω K.canonicalTopologicalData.uniformizerUnit : ℂ) * X)
          else 1

set_option maxHeartbeats 1000000 in
/-- Evaluate the rank-one block factors on the two ordered Langlands data. -/
theorem sphericalPairTwistLPolynomial : SphericalPairTwistLPolynomialStatement.{u} := by
  classical
  intro p _ K r t ψ ν hν A Aω B s s' hs hs' ω hω P hP
  obtain ⟨x, hx, rfl, hA⟩ := exists_unramifiedDatum_isLanglandsQuotient K A A.obj
    (Representation.Equiv.refl _) s hs
  obtain ⟨y, hy, rfl, hB⟩ := exists_unramifiedDatum_isLanglandsQuotient K B B.obj
    (Representation.Equiv.refl _) s' hs'
  obtain ⟨A₀, Aω₀, hA₀, hAω₀, ⟨e₀⟩⟩ := hω
  obtain ⟨f⟩ := (automorphicClassOf_eq_iff K A₀ A).mp hA₀
  obtain ⟨g⟩ := (automorphicClassOf_eq_iff K Aω₀ Aω).mp hAω₀
  let e := ((Langlands.twistEquiv (determinantQuasiCharacter K r.succPNat ω) f.symm).trans
    e₀).trans g
  let μ (i : Fin (r + 1)) := character K (x i) * ω
  let d := characterDatum.{u,u} K μ (monotone_unramifiedCharacter_mul K x hx ω)
  let d' := unramifiedDatum.{u,u} K y hy
  have hAω : d.IsLanglandsQuotient Aω.obj :=
    unramifiedDatum_twist_isLanglandsQuotient K x hx ω A.obj Aω.obj hA e
  have hL := (isAutomorphicPairLPolynomial_iff K Aω B Aω.obj B.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hP
  obtain ⟨P₀, Q, hP₀, hQ, hprod⟩ := squareIntegrableDataLFactor.{u,u,u} p K ψ ⟨ν, hν⟩
    r t d d' Aω.obj B.obj hAω hB
  have hBlock (i : Fin d.shape.length) (j : Fin d'.shape.length) :
      Q i j = lPolynomial K.canonicalTopologicalData (μ i * character K (y j)) := by
    have h := isPadicPairLPolynomial_of_rankOneCharacterEquiv K ψ ν
      (FiniteRepresentation.characterLineEquiv.{u,u} (determinantQuasiCharacter K 1 (μ i))).symm
      (FiniteRepresentation.characterLineEquiv.{u,u}
        (determinantQuasiCharacter K 1 (character K (y j)))).symm
    exact (isPadicRankLPolynomial_succ.mp (hQ i j)).unique
      ((isPadicSymmetricLPolynomial_of_le (Nat.le_refl 0)).mpr h)
  rw [hL.unique hP₀, hprod]
  simp_rw [hBlock, μ, lPolynomial_character_mul_twist]
  by_cases h : K.canonicalTopologicalData.multiplicativeConductor ω = 0
  · simp only [h, ite_true, pairEulerPolynomial_ofTuple, Polynomial.prod_comp]
    rfl
  · simp [h]

end Langlands.Correspondence
