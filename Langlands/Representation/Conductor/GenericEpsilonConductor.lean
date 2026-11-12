import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor
import Langlands.Representation.RankinSelberg.UniformRankOneTwistProof
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.LocalField.Normalization.Proof
import Langlands.Representation.Conductor.EssentialStatement
import Langlands.Representation.RankinSelberg.PairEpsilonNormalizationStatement

/-!
# Epsilon-factor conductors of generic p-adic representations and pairs

For generic representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)` over a p-adic
field, the constructed JPSS epsilon factor at the actual self-dual Haar measure of `ψ` is
`c q^(-f(π × σ, ψ) s)`. Bushnell, Henniart and Kutzko write
`f(π × σ, ψ) = (r+1)(n+1) c(ψ) + f(π × σ)`, with `c(ψ)` the largest integer `c` such that
`ψ` is trivial on `𝔭^(-c)`; JPSS 1981 define the conductor of `π` from the epsilon factor
for `ψ` of conductor `𝔒`, where `c(ψ) = 0`. This file constructs `f(π × σ, ψ)`,
`f(π × σ)` and `f(π) = f(π × 1)` from the proved epsilon existence and proves their
characterizations. Independence of `ψ`, nonnegativity and the newvector interpretation
are not proved here; the last section derives them from the published, unproved
statements supplied as hypotheses.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear

universe uF uV uW uV₂ uW₂

private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance genericConductorNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance genericConductorValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance genericConductorLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance genericConductorNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier :=
  valuative_nonarchimedean
local instance genericConductorMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance genericConductorBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

/-! ### Additive characters of conductor `𝔒` -/

/-- A character of conductor `𝔒` in Jacquet's sense has additive conductor exponent `0`:
it is trivial on `𝔒 = 𝔭^0` and nontrivial on `𝔭^(-1)`. -/
theorem additiveConductor_eq_zero_of_hasIntegerConductor
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ) :
    F.canonicalTopologicalData.additiveConductor ψ = 0 := by
  let T := F.canonicalTopologicalData
  apply le_antisymm
  · by_contra h
    have hc : (1 : ℤ) ≤ T.additiveConductor ψ := by
      change (1 : ℤ) ≤ F.canonicalTopologicalData.additiveConductor ψ
      omega
    have h1 : T.AdditiveTrivialAt ψ 1 := (T.additiveTrivialAt_iff_le_conductor ψ 1).mpr hc
    have hu : (T.uniformizer : F.Carrier) ≠ 0 := by
      intro h0
      have hv := T.discreteValuation_uniformizer
      rw [h0, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    have hx : (T.uniformizer⁻¹ : F.Carrier) ∈ (ValuativeRel.valuation F.Carrier).integer := by
      refine hψ.2 _ fun y hy => h1 _ ?_
      rw [T.mem_additiveLattice_iff_div_mem_integers]
      have : T.uniformizer⁻¹ * y / T.uniformizer ^ (-(1 : ℤ)) = y := by
        rw [zpow_neg, zpow_one, div_inv_eq_mul, mul_comm, ← mul_assoc,
          mul_inv_cancel₀ hu, one_mul]
      rw [this]
      exact hy
    have h2 : (1 : F.Carrier) ∈ T.additiveLattice (-1) := by
      rw [T.mem_additiveLattice_iff_div_mem_integers]
      simpa using hx
    rw [T.mem_additiveLattice, map_one, ← WithZero.exp_zero] at h2
    have := WithZero.exp_le_exp.mp h2
    omega
  · exact (T.additiveTrivialAt_iff_le_conductor ψ 0).mp
      fun x hx => hψ.1 x ((T.mem_additiveLattice_zero x).mp hx)

/-- The two descriptions of characters of conductor `𝔒` agree. -/
theorem additiveConductor_eq_zero_iff_hasIntegerConductor
    (ψ : UnitaryAdditiveCharacter F.Carrier) :
    F.canonicalTopologicalData.additiveConductor ψ = 0 ↔ HasIntegerConductor ψ :=
  ⟨HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero F ψ,
    additiveConductor_eq_zero_of_hasIntegerConductor F ψ⟩

/-! ### The epsilon exponent and the conductor of a generic pair -/

section Pair

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The coefficient and exponent of the constructed epsilon factor of the pair at the actual
self-dual Haar measure of `ψ`, read with the larger rank first. -/
def genericPairEpsilonCoefficientExponent : ℂˣ × ℤ :=
  genericSymmetricEpsilonData F ψ (Correspondence.localSelfDualHaar F ψ)
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) π σ hπ hσ

/-- Bushnell–Henniart–Kutzko's `f(π × σ, ψ)`: the integer with
`ε(s, π × σ, ψ) = ε(0, π × σ, ψ) q^(-f(π × σ, ψ) s)`. -/
def genericPairEpsilonExponent : ℤ :=
  (genericPairEpsilonCoefficientExponent F ψ π σ hπ hσ).2

/-- The constructed data satisfy the full p-adic epsilon relation at every self-dual Haar
measure of `ψ`. -/
theorem genericPairEpsilonCoefficientExponent_isPadic
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    IsPadicSymmetricEpsilonFactor F ψ ν π σ
      (genericPairEpsilonCoefficientExponent F ψ π σ hπ hσ) := by
  have hν' : ν = Correspondence.localSelfDualHaar F ψ :=
    Correspondence.eq_localSelfDualHaar F ψ ν hν
  subst hν'
  exact genericSymmetricEpsilonData_isPadic F ψ _ _ π σ hπ hσ

/-- At every self-dual Haar measure, every certified epsilon factor has the constructed
coefficient and exponent. -/
theorem genericPairEpsilonCoefficientExponent_eq
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) {e : ℂˣ × ℤ}
    (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    genericPairEpsilonCoefficientExponent F ψ π σ hπ hσ = e :=
  (genericPairEpsilonCoefficientExponent_isPadic F ψ π σ hπ hσ ν hν).unique he

/-- Agreement with the published constructor at any supplied self-dual Haar measure. -/
theorem genericPairEpsilonCoefficientExponent_eq_genericSymmetricEpsilonData
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    genericPairEpsilonCoefficientExponent F ψ π σ hπ hσ =
      genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ :=
  genericPairEpsilonCoefficientExponent_eq F ψ π σ hπ hσ ν hν
    (genericSymmetricEpsilonData_isPadic F ψ ν hν π σ hπ hσ)

/-- The exponent of every certified epsilon factor at a self-dual measure. -/
theorem genericPairEpsilonExponent_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {e : ℂˣ × ℤ} (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    genericPairEpsilonExponent F ψ π σ hπ hσ = e.2 := by
  rw [genericPairEpsilonExponent, genericPairEpsilonCoefficientExponent_eq F ψ π σ hπ hσ ν hν he]

/-- Bushnell–Henniart–Kutzko's conductor of the pair,
`f(π × σ) = f(π × σ, ψ) - (r+1)(n+1) c(ψ)`, where `c(ψ)` is the additive conductor
exponent. -/
def genericPairConductor : ℤ :=
  genericPairEpsilonExponent F ψ π σ hπ hσ -
    ((r + 1) * (n + 1) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ

/-- The conductor of the pair read off from any certified epsilon factor. -/
theorem genericPairConductor_eq (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    {e : ℂˣ × ℤ} (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    genericPairConductor F ψ π σ hπ hσ =
      e.2 - ((r + 1) * (n + 1) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ := by
  rw [genericPairConductor, genericPairEpsilonExponent_eq F ψ π σ hπ hσ ν hν he]

/-- For `ψ` of conductor `𝔒` the conductor of the pair is the epsilon exponent. -/
theorem genericPairConductor_eq_epsilonExponent (hψ : HasIntegerConductor ψ) :
    genericPairConductor F ψ π σ hπ hσ = genericPairEpsilonExponent F ψ π σ hπ hσ := by
  rw [genericPairConductor, additiveConductor_eq_zero_of_hasIntegerConductor F ψ hψ,
    mul_zero, sub_zero]

variable {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}

/-- The constructed coefficient and exponent depend only on the equivalence classes. -/
theorem genericPairEpsilonCoefficientExponent_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) :
    genericPairEpsilonCoefficientExponent F ψ π σ hπ hσ =
      genericPairEpsilonCoefficientExponent F ψ π₂ σ₂ hπ₂ hσ₂ := by
  apply genericPairEpsilonCoefficientExponent_eq F ψ π σ hπ hσ
    (Correspondence.localSelfDualHaar F ψ) (Correspondence.isSelfDual_localSelfDualHaar F ψ)
  exact (IsPadicSymmetricEpsilonFactor.congr_equiv φ φ').mpr
    (genericPairEpsilonCoefficientExponent_isPadic F ψ π₂ σ₂ hπ₂ hσ₂ _
      (Correspondence.isSelfDual_localSelfDualHaar F ψ))

/-- The conductor of a pair depends only on the equivalence classes. -/
theorem genericPairConductor_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) :
    genericPairConductor F ψ π σ hπ hσ = genericPairConductor F ψ π₂ σ₂ hπ₂ hσ₂ := by
  rw [genericPairConductor, genericPairConductor, genericPairEpsilonExponent,
    genericPairEpsilonExponent,
    genericPairEpsilonCoefficientExponent_congr_equiv F ψ π σ hπ hσ φ φ' hπ₂ hσ₂]

end Pair

/-! ### The conductor of a generic representation -/

/-- The trivial character of `GL_1` is generic (the published theorem, restated for the
local instances of this file). -/
private theorem isGeneric_trivialRankOneCharacter (ψ : UnitaryAdditiveCharacter F.Carrier) :
    Whittaker.IsGeneric ψ 0 (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) :=
  UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ

section Single

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (hπ : Whittaker.IsGeneric ψ r π)

/-- The conductor `f(π) = f(π × 1)` of a generic representation: the conductor of its pair
with the trivial character of `GL_1`. -/
def genericConductor : ℤ :=
  genericPairConductor F ψ π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hπ
    (isGeneric_trivialRankOneCharacter F ψ)

/-- The conductor read off from the epsilon relation used in `ConductorExponentStatement`:
if `ε(s, π × 1, ψ) = c q^(-ms)` at a self-dual measure, then `f(π) = m - (r+1) c(ψ)`. -/
theorem genericConductor_eq (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    {c : ℂˣ} {m : ℤ}
    (h : IsPadicPairEpsilonFactor F ψ ν π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) (c, m)) :
    genericConductor F ψ π hπ =
      m - ((r + 1 : ℕ) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ := by
  rw [genericConductor, genericPairConductor_eq F ψ π _ hπ _ ν hν
    ((isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mpr h)]
  push_cast
  ring

/-- JPSS 1981, (1.1): for `ψ` of conductor `𝔒`, the conductor of `π` is the exponent `m` in
`ε(s, π × 1, ψ) = c q^(-ms)`. -/
theorem genericConductor_eq_of_hasIntegerConductor (hψ : HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) {c : ℂˣ} {m : ℤ}
    (h : IsPadicPairEpsilonFactor F ψ ν π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) (c, m)) :
    genericConductor F ψ π hπ = m := by
  rw [genericConductor_eq F ψ π hπ ν hν h,
    additiveConductor_eq_zero_of_hasIntegerConductor F ψ hψ, mul_zero, sub_zero]

/-- The constructed epsilon factor of `π × 1` exists with exponent
`f(π) + (r+1) c(ψ)` at every self-dual measure. -/
theorem exists_isPadicPairEpsilonFactor_genericConductor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    ∃ c : ℂˣ, IsPadicPairEpsilonFactor F ψ ν π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (c, genericConductor F ψ π hπ +
        ((r + 1 : ℕ) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ) := by
  let h1 := isGeneric_trivialRankOneCharacter F ψ
  have hspec := genericPairEpsilonCoefficientExponent_isPadic F ψ π
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hπ h1 ν hν
  refine ⟨(genericPairEpsilonCoefficientExponent F ψ π _ hπ h1).1, ?_⟩
  have hexp : genericConductor F ψ π hπ +
      ((r + 1 : ℕ) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ =
      (genericPairEpsilonCoefficientExponent F ψ π _ hπ h1).2 := by
    rw [genericConductor, genericPairConductor, genericPairEpsilonExponent]
    push_cast
    ring
  rw [hexp]
  exact (isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mp hspec

variable {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}

/-- The conductor depends only on the equivalence class. -/
theorem genericConductor_congr_equiv (φ : π.Equiv π₂) (hπ₂ : Whittaker.IsGeneric ψ r π₂) :
    genericConductor F ψ π hπ = genericConductor F ψ π₂ hπ₂ :=
  genericPairConductor_congr_equiv F ψ π _ hπ _ φ (Representation.Equiv.refl _) hπ₂ _

end Single

/-! ### Comparison with the published conductor statements

These theorems assume the published, unproved statements as explicit hypotheses. They show
that the constructed integers are the integers those statements assert, and prove nothing
about the statements themselves. -/

section Statements

/-- Given `PairEpsilonExponentStatement` (Bushnell–Henniart–Kutzko 1998, printed p.703), the
constructed conductor of a generic pair does not depend on the additive character. -/
theorem genericPairConductor_eq_of_pairEpsilonExponentStatement
    (hS : PairEpsilonExponentStatement.{uF, uV, uW})
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ψ ψ' : UnitaryAdditiveCharacter F.Carrier)
    (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)
    (hπ' : Whittaker.IsGeneric ψ' r π) (hσ' : Whittaker.IsGeneric ψ' n σ) :
    genericPairConductor F ψ π σ hπ hσ = genericPairConductor F ψ' π σ hπ' hσ' := by
  obtain ⟨a, ha⟩ := hS p F r n π σ hπ.1 hπ.2.1 hσ.1 hσ.2.1
  have key (χ : UnitaryAdditiveCharacter F.Carrier) (hπχ : Whittaker.IsGeneric χ r π)
      (hσχ : Whittaker.IsGeneric χ n σ) : genericPairConductor F χ π σ hπχ hσχ = a := by
    have he := ha χ ⟨Correspondence.localSelfDualHaar F χ,
      Correspondence.isSelfDual_localSelfDualHaar F χ⟩
      (genericPairEpsilonCoefficientExponent F χ π σ hπχ hσχ)
      (genericPairEpsilonCoefficientExponent_isPadic F χ π σ hπχ hσχ _
        (Correspondence.isSelfDual_localSelfDualHaar F χ))
    rw [genericPairConductor, genericPairEpsilonExponent, he]
    push_cast
    ring
  rw [key ψ hπ hσ, key ψ' hπ' hσ']

/-- Given JPSS 1981, Théorème (5.1) (`ConductorExponentStatement`), for `ψ` of conductor `𝔒`
the constructed conductor of a generic representation is a natural number `m`, it is the
least level with nonzero `K_(r+1)(m)`-fixed vectors, and the level-`m` fixed space is a
line. -/
theorem genericConductor_isNewvectorConductor_of_conductorExponentStatement
    (hC : ConductorExponentStatement.{uF, uV})
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ r π) :
    ∃ m : ℕ, genericConductor F ψ π hπ = m ∧ IsNewvectorConductor π m ∧
      Module.finrank ℂ (levelFixedVectors π m) = 1 := by
  obtain ⟨ϖ, hϖ, hϖabs⟩ := HighlyRamified.exists_uniformizingElement_normalizedAbs F
  obtain ⟨c, m, hε, hnew, hdim⟩ := @hC F.Carrier _ _ _ _ _ _ (borel F.Carrier) ⟨rfl⟩
    (borel _) (@BorelSpace.mk _ _ (borel _) rfl) (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
    (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
    F.canonicalTopologicalData.residueCardinality rfl
    (normalizedAbsoluteValue F.canonicalTopologicalData) ϖ hϖ hϖabs
    (HighlyRamified.normalizedAbsoluteValue_eq_one F) ψ hψ
    (Correspondence.localSelfDualHaar F ψ) (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    r V _ _ π hπ
  exact ⟨m, genericConductor_eq_of_hasIntegerConductor F ψ π hπ hψ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) hε, hnew, hdim⟩

end Statements

end Langlands.Conductor
