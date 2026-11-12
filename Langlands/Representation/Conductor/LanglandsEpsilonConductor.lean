import Langlands.Representation.Conductor.GenericEpsilonConductor
import Langlands.Representation.RankinSelberg.LanglandsPairEpsilonBlockExistence
import Langlands.Representation.RankinSelberg.LanglandsFactorDescent
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonStatement
import Langlands.Correspondence.RankOneExistence

/-!
# Epsilon-factor conductors of irreducible pairs through Langlands data

For irreducible smooth representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`, generic
or not, the Library constructs the epsilon factor of the pair from square-integrable Langlands
data (Henniart 2002, 2.8), given square-integrable exhaustion and classification. This file
reads off the epsilon exponent `f(π × σ, ψ)`, the conductor
`f(π × σ) = f(π × σ, ψ) - (r+1)(t+1) c(ψ)` and the conductor `f(π) = f(π × 1)` at the actual
self-dual Haar measure of `ψ`. The classification inputs stay explicit hypotheses. Under the
published comparison statement for generic pairs, these conductors are the generic ones of
`Conductor.GenericEpsilonConductor`.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear Classification

universe uF uV uW

private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance langlandsConductorNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance langlandsConductorValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance langlandsConductorLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance langlandsConductorNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier :=
  valuative_nonarchimedean
local instance langlandsConductorMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance langlandsConductorBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

/-- An irreducible quotient is transported along an equivalence of the quotient. -/
private theorem isIrreducibleQuotient_of_equiv_target {G : Type*} [Group G]
    {V W W' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} {π' : Representation ℂ G W'} (e : π.Equiv π')
    (h : IsIrreducibleQuotient ρ π) : IsIrreducibleQuotient ρ π' := by
  obtain ⟨hπ, q, hq⟩ := h
  refine ⟨?_, e.toIntertwiningMap.comp q, fun w => ?_⟩
  · rw [Representation.irreducible_iff_isSimpleModule_asModule] at hπ ⊢
    exact (LinearMap.isSimpleModule_iff_of_bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
      e.bijective).1 hπ
  · obtain ⟨v, hv⟩ := hq (e.symm w)
    exact ⟨v, by simp [Representation.IntertwiningMap.comp_apply, hv]⟩

/-- The actual self-dual Haar measure of `ψ` with its self-duality proof. -/
private def selfDualPoint (ψ : UnitaryAdditiveCharacter F.Carrier) :
    LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ :=
  ⟨Correspondence.localSelfDualHaar F ψ, Correspondence.isSelfDual_localSelfDualHaar F ψ⟩

/-! ### The epsilon exponent and the conductor of an irreducible pair -/

section Pair

variable {r t : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (σ : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))
  (hπ : Representation.IsIrreducible π.representation)
  (hσ : Representation.IsIrreducible σ.representation)
  (hexπ : SquareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData)
  (hexσ : SquareIntegrableLanglandsExhaustion.{uF, uW} F F.canonicalTopologicalData)
  (hclπ : SquareIntegrableLanglandsClassification.{uF, uV} F F.canonicalTopologicalData)
  (hclσ : SquareIntegrableLanglandsClassification.{uF, uW} F F.canonicalTopologicalData)

/-- The coefficient and exponent `(c, m)` of the epsilon factor `c q^(-ms)` of the pair,
constructed from square-integrable Langlands data at the actual self-dual Haar measure. -/
def langlandsPairEpsilonCoefficientExponent : ℂˣ × ℤ :=
  (langlandsPairEpsilonFactorOfClassification F ψ (Correspondence.localSelfDualHaar F ψ) π σ
    hπ hσ hexπ hexσ hclπ hclσ
    (fun d d' _ _ => squareIntegrableDataEpsilonExistence.{uF, uV, uW} F ψ
      (selfDualPoint F ψ) d d')).val

/-- The constructed data are the Langlands-data epsilon factor at every self-dual measure. -/
theorem langlandsPairEpsilonCoefficientExponent_isLanglands
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ
      (langlandsPairEpsilonCoefficientExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ) := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  exact (langlandsPairEpsilonFactorOfClassification F ψ _ π σ hπ hσ hexπ hexσ hclπ hclσ
    (fun d d' _ _ => squareIntegrableDataEpsilonExistence.{uF, uV, uW} F ψ
      (selfDualPoint F ψ) d d')).property

/-- Every Langlands-data epsilon factor at a self-dual measure is the constructed one. -/
theorem langlandsPairEpsilonCoefficientExponent_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {e : ℂˣ × ℤ}
    (he : IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e) :
    langlandsPairEpsilonCoefficientExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ = e :=
  (langlandsPairEpsilonCoefficientExponent_isLanglands F ψ π σ hπ hσ hexπ hexσ hclπ hclσ
    ν hν).unique he

/-- `f(π × σ, ψ)`: the exponent of the Langlands-data epsilon factor. -/
def langlandsPairEpsilonExponent : ℤ :=
  (langlandsPairEpsilonCoefficientExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ).2

/-- `f(π × σ) = f(π × σ, ψ) - (r+1)(t+1) c(ψ)`, with `c(ψ)` the additive conductor
exponent. -/
def langlandsPairConductor : ℤ :=
  langlandsPairEpsilonExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ -
    ((r + 1) * (t + 1) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ

/-- The conductor read off from any Langlands-data epsilon factor at a self-dual measure. -/
theorem langlandsPairConductor_eq (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    {e : ℂˣ × ℤ}
    (he : IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e) :
    langlandsPairConductor F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      e.2 - ((r + 1) * (t + 1) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ := by
  rw [langlandsPairConductor, langlandsPairEpsilonExponent,
    langlandsPairEpsilonCoefficientExponent_eq F ψ π σ hπ hσ hexπ hexσ hclπ hclσ ν hν he]

/-- For `ψ` of conductor `𝔒` the conductor of the pair is the epsilon exponent. -/
theorem langlandsPairConductor_eq_epsilonExponent (hψ : HasIntegerConductor ψ) :
    langlandsPairConductor F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      langlandsPairEpsilonExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ := by
  rw [langlandsPairConductor, additiveConductor_eq_zero_of_hasIntegerConductor F ψ hψ,
    mul_zero, sub_zero]

/-- For any square-integrable data `d`, `d'` presenting `π` and `σ` and any epsilon factors
`b i j` of their block pairs at a self-dual measure, `f(π × σ, ψ)` is the sum of the block
exponents. -/
theorem langlandsPairEpsilonExponent_eq_sum (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν)
    (d : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1))
    (d' : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{max uF uW, uF}
      F.canonicalTopologicalData (t + 1))
    (hd : d.IsLanglandsQuotient π) (hd' : d'.IsLanglandsQuotient σ)
    (b : Fin d.shape.length → Fin d'.shape.length → ℂˣ × ℤ)
    (hb : ∀ i j, IsPadicRankEpsilonFactor F ψ ν (d.blocks i).representation
      (d'.blocks j).representation (b i j)) :
    langlandsPairEpsilonExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ = ∑ i, ∑ j, (b i j).2 := by
  have h := ((langlandsPairEpsilonCoefficientExponent_isLanglands F ψ π σ hπ hσ hexπ hexσ
    hclπ hclσ ν hν).2.2 d d' hd hd').unique ⟨b, hb, rfl⟩
  rw [langlandsPairEpsilonExponent, h]
  rfl

/-- In the same situation, `f(π × σ)` is the sum over the block pairs of
`f(π_i × σ_j, ψ) - n_i n'_j c(ψ)`, where `n_i` and `n'_j` are the block ranks. -/
theorem langlandsPairConductor_eq_sum (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν)
    (d : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1))
    (d' : PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{max uF uW, uF}
      F.canonicalTopologicalData (t + 1))
    (hd : d.IsLanglandsQuotient π) (hd' : d'.IsLanglandsQuotient σ)
    (b : Fin d.shape.length → Fin d'.shape.length → ℂˣ × ℤ)
    (hb : ∀ i j, IsPadicRankEpsilonFactor F ψ ν (d.blocks i).representation
      (d'.blocks j).representation (b i j)) :
    langlandsPairConductor F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      ∑ i, ∑ j, ((b i j).2 - ((d.shape.size i : ℤ) * d'.shape.size j) *
        F.canonicalTopologicalData.additiveConductor ψ) := by
  have h₁ : ((r + 1 : ℕ) : ℤ) = ∑ i, (d.shape.size i : ℤ) := by
    rw [← Nat.cast_sum, d.shape.sum_eq]
  have h₂ : ((t + 1 : ℕ) : ℤ) = ∑ j, (d'.shape.size j : ℤ) := by
    rw [← Nat.cast_sum, d'.shape.sum_eq]
  push_cast at h₁ h₂
  rw [langlandsPairConductor,
    langlandsPairEpsilonExponent_eq_sum F ψ π σ hπ hσ hexπ hexσ hclπ hclσ ν hν d d' hd hd' b hb,
    h₁, h₂, Finset.sum_mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- The Langlands-data epsilon relation is unchanged when `π` and `σ` are replaced by
equivalent representations. -/
theorem isLanglandsPairEpsilonFactor_of_equiv
    {π₂ : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
    {σ₂ : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}
    (φ : π.representation.Equiv π₂.representation)
    (φ' : σ.representation.Equiv σ₂.representation)
    (ν : AdditiveHaarMeasure F.Carrier) {e : ℂˣ × ℤ}
    (he : IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e) :
    IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π₂ σ₂ e := by
  obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩, h⟩ := he
  exact ⟨⟨d, isIrreducibleQuotient_of_equiv_target φ hd⟩,
    ⟨d', isIrreducibleQuotient_of_equiv_target φ' hd'⟩, fun a a' ha ha' =>
      h a a' (isIrreducibleQuotient_of_equiv_target φ.symm ha)
        (isIrreducibleQuotient_of_equiv_target φ'.symm ha')⟩

/-- The constructed epsilon data are unchanged when `π` and `σ` are replaced by equivalent
representations. -/
theorem langlandsPairEpsilonCoefficientExponent_congr_equiv
    {π₂ : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
    {σ₂ : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}
    (φ : π.representation.Equiv π₂.representation)
    (φ' : σ.representation.Equiv σ₂.representation)
    (hπ₂ : Representation.IsIrreducible π₂.representation)
    (hσ₂ : Representation.IsIrreducible σ₂.representation) :
    langlandsPairEpsilonCoefficientExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      langlandsPairEpsilonCoefficientExponent F ψ π₂ σ₂ hπ₂ hσ₂ hexπ hexσ hclπ hclσ :=
  (langlandsPairEpsilonCoefficientExponent_eq F ψ π₂ σ₂ hπ₂ hσ₂ hexπ hexσ hclπ hclσ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    (isLanglandsPairEpsilonFactor_of_equiv F ψ π σ φ φ' _
      (langlandsPairEpsilonCoefficientExponent_isLanglands F ψ π σ hπ hσ hexπ hexσ hclπ hclσ _
        (Correspondence.isSelfDual_localSelfDualHaar F ψ)))).symm

/-- The conductor of the pair is unchanged when `π` and `σ` are replaced by equivalent
representations. -/
theorem langlandsPairConductor_congr_equiv
    {π₂ : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
    {σ₂ : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}
    (φ : π.representation.Equiv π₂.representation)
    (φ' : σ.representation.Equiv σ₂.representation)
    (hπ₂ : Representation.IsIrreducible π₂.representation)
    (hσ₂ : Representation.IsIrreducible σ₂.representation) :
    langlandsPairConductor F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      langlandsPairConductor F ψ π₂ σ₂ hπ₂ hσ₂ hexπ hexσ hclπ hclσ := by
  rw [langlandsPairConductor, langlandsPairConductor, langlandsPairEpsilonExponent,
    langlandsPairEpsilonExponent,
    langlandsPairEpsilonCoefficientExponent_congr_equiv F ψ π σ hπ hσ hexπ hexσ hclπ hclσ φ φ'
      hπ₂ hσ₂]

/-- Given the published comparison statement, for a generic pair the Langlands-data
epsilon data are the constructed generic epsilon data. -/
theorem langlandsPairEpsilonCoefficientExponent_eq_generic
    (h : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, max uF uV, max uF uW})
    (hπg : Whittaker.IsGeneric ψ r π.representation)
    (hσg : Whittaker.IsGeneric ψ t σ.representation) :
    langlandsPairEpsilonCoefficientExponent F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      genericPairEpsilonCoefficientExponent F ψ π.representation σ.representation hπg hσg :=
  (genericPairEpsilonCoefficientExponent_eq F ψ π.representation σ.representation hπg hσg _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    (h p F ψ (selfDualPoint F ψ) r t π σ hπg hσg _
      (langlandsPairEpsilonCoefficientExponent_isLanglands F ψ π σ hπ hσ hexπ hexσ hclπ hclσ _
        (Correspondence.isSelfDual_localSelfDualHaar F ψ)))).symm

/-- Given the published comparison statement, for a generic pair the conductor through
Langlands data is the generic conductor. -/
theorem langlandsPairConductor_eq_generic
    (h : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, max uF uV, max uF uW})
    (hπg : Whittaker.IsGeneric ψ r π.representation)
    (hσg : Whittaker.IsGeneric ψ t σ.representation) :
    langlandsPairConductor F ψ π σ hπ hσ hexπ hexσ hclπ hclσ =
      genericPairConductor F ψ π.representation σ.representation hπg hσg := by
  rw [langlandsPairConductor, genericPairConductor, langlandsPairEpsilonExponent,
    genericPairEpsilonExponent,
    langlandsPairEpsilonCoefficientExponent_eq_generic F ψ π σ hπ hσ hexπ hexσ hclπ hclσ h
      hπg hσg]

end Pair

/-! ### The conductor of an irreducible representation -/

/-- The trivial character of `GL_1(F)` as a smooth representation on a lifted complex line:
the published `Correspondence.rankOneCharacterObject` at the trivial quasicharacter. -/
abbrev trivialRankOneObject :
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear 1 F.Carrier) :=
  Correspondence.rankOneCharacterObject.{uF, max uF uV} F 1

theorem trivialRankOneObject_isIrreducible :
    Representation.IsIrreducible (trivialRankOneObject.{uF, uV} F).representation :=
  FiniteRepresentation.characterLine_isIrreducible _

section Single

variable {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (hπ : Representation.IsIrreducible π.representation)
  (hex : SquareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData)
  (hcl : SquareIntegrableLanglandsClassification.{uF, uV} F F.canonicalTopologicalData)

/-- `f(π) = f(π × 1)`: the conductor of the pair of `π` with the trivial character of
`GL_1`, through Langlands data. -/
def langlandsConductor : ℤ :=
  langlandsPairConductor.{uF, uV, uV} F ψ π (trivialRankOneObject.{uF, uV} F) hπ
    (trivialRankOneObject_isIrreducible F) hex hex hcl hcl

/-- If `(c, m)` is the Langlands-data epsilon factor of `π × 1` at a self-dual measure, then
`f(π) = m - (r+1) c(ψ)`. -/
theorem langlandsConductor_eq (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    {c : ℂˣ} {m : ℤ}
    (he : IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uV} F ψ ν π
      (trivialRankOneObject.{uF, uV} F) (c, m)) :
    langlandsConductor F ψ π hπ hex hcl =
      m - ((r + 1 : ℕ) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ := by
  rw [langlandsConductor, langlandsPairConductor_eq F ψ π _ hπ _ hex hex hcl hcl ν hν he]
  push_cast
  ring

/-- For `ψ` of conductor `𝔒`, `f(π)` is the exponent of the epsilon factor of `π × 1`. -/
theorem langlandsConductor_eq_of_hasIntegerConductor (hψ : HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) {c : ℂˣ} {m : ℤ}
    (he : IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uV} F ψ ν π
      (trivialRankOneObject.{uF, uV} F) (c, m)) :
    langlandsConductor F ψ π hπ hex hcl = m := by
  rw [langlandsConductor_eq F ψ π hπ hex hcl ν hν he,
    additiveConductor_eq_zero_of_hasIntegerConductor F ψ hψ, mul_zero, sub_zero]

/-- At every self-dual measure, `π × 1` has a Langlands-data epsilon factor
`c q^(-(f(π) + (r+1) c(ψ)) s)`. -/
theorem exists_isLanglandsPairEpsilonFactor_langlandsConductor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    ∃ c : ℂˣ, IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uV} F ψ ν π
      (trivialRankOneObject.{uF, uV} F)
      (c, langlandsConductor F ψ π hπ hex hcl +
        ((r + 1 : ℕ) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ) := by
  refine ⟨(langlandsPairEpsilonCoefficientExponent F ψ π (trivialRankOneObject.{uF, uV} F) hπ
    (trivialRankOneObject_isIrreducible F) hex hex hcl hcl).1, ?_⟩
  have hX : langlandsConductor F ψ π hπ hex hcl +
      ((r + 1 : ℕ) : ℤ) * F.canonicalTopologicalData.additiveConductor ψ =
      (langlandsPairEpsilonCoefficientExponent F ψ π (trivialRankOneObject.{uF, uV} F) hπ
        (trivialRankOneObject_isIrreducible F) hex hex hcl hcl).2 := by
    rw [langlandsConductor, langlandsPairConductor, langlandsPairEpsilonExponent]
    push_cast
    ring
  rw [hX]
  exact langlandsPairEpsilonCoefficientExponent_isLanglands F ψ π _ hπ
    (trivialRankOneObject_isIrreducible F) hex hex hcl hcl ν hν

/-- `f(π)` is unchanged when `π` is replaced by an equivalent representation. -/
theorem langlandsConductor_congr_equiv
    {π₂ : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
    (φ : π.representation.Equiv π₂.representation)
    (hπ₂ : Representation.IsIrreducible π₂.representation) :
    langlandsConductor F ψ π hπ hex hcl = langlandsConductor F ψ π₂ hπ₂ hex hcl :=
  langlandsPairConductor_congr_equiv F ψ π _ hπ _ hex hex hcl hcl φ
    (Representation.Equiv.refl _) hπ₂ _

/-- The lifted trivial character line is equivalent to the scalar trivial character of
`GL_1` used by the generic conductor. -/
def trivialRankOneObjectEquiv :
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv
      (trivialRankOneObject.{uF, uV} F).representation :=
  Representation.Equiv.mk (ULift.moduleEquiv : ULift.{max uF uV} ℂ ≃ₗ[ℂ] ℂ).symm
    (fun _ => rfl)

/-- Given the published comparison statement, for generic `π` the conductor through
Langlands data is the generic conductor `genericConductor`. -/
theorem langlandsConductor_eq_genericConductor
    (h : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, max uF uV, max uF uV})
    (hπg : Whittaker.IsGeneric ψ r π.representation) :
    langlandsConductor F ψ π hπ hex hcl = genericConductor F ψ π.representation hπg := by
  have h1 : Whittaker.IsGeneric ψ 0 (trivialRankOneObject.{uF, uV} F).representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ 0 (trivialRankOneObjectEquiv F)).mp
      (UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ)
  rw [langlandsConductor, langlandsPairConductor_eq_generic F ψ π _ hπ _ hex hex hcl hcl h
    hπg h1, genericConductor]
  exact (genericPairConductor_congr_equiv F ψ π.representation _ hπg _
    (Representation.Equiv.refl _) (trivialRankOneObjectEquiv F) hπg _).symm

end Single

end Langlands.Conductor
