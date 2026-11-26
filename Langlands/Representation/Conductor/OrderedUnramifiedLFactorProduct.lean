import Langlands.Representation.Conductor.OrderedUnramifiedTemperedType
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof

/-!
# `L(s, π × I(x)) = ∏_j L(s, π × χ_(x_j))` for norm-ordered `x`, from the premises

Over a nonarchimedean local field `F`, assume the three results of JPSS 1983, Section 9,
over `F`: the classification of generic representations with the identification of
Whittaker models (`GenericStandardModuleStatement`), the pole bound (8.4)
(`TemperedPoleBoundStatement`) and the tail divisibility (9.3) (`InducedTailLFactorAt`).
For an irreducible admissible generic `π` and `|x_1| ≤ ⋯ ≤ |x_(n+1)|`, the L-polynomial of
`π × I(x)` is the product of the L-polynomials of the pairs `π × χ_(x_j)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Conductor.OrderedUnramifiedTemperedType

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.Conductor.UnramifiedPrincipalSeries
open Langlands.AllField.RankinSelberg
open _root_.Polynomial

universe uF uV uW uV₂ uW₂

section Congruence

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  {ψ : UnitaryAdditiveCharacter F} {ν : letI := borel F; AdditiveHaarMeasure F}
  {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (GeneralLinear (n + 1) F) W₂}

/-- The pair L-polynomial relation depends only on the two Whittaker-function sets used
by its zeta integrals. -/
theorem isPadicPairLPolynomial_congr_whittakerSets
    (hπ : RankinSelberg.whittakerSet ψ r π = RankinSelberg.whittakerSet ψ r π₂)
    (hσ : RankinSelberg.inverseWhittakerSet ψ n σ = RankinSelberg.inverseWhittakerSet ψ n σ₂)
    {P : ℂ[X]} :
    IsPadicPairLPolynomial F ψ ν π σ P ↔ IsPadicPairLPolynomial F ψ ν π₂ σ₂ P := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (GeneralLinear (n + 1) F)
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (RankinSelberg.LeftUnipotentQuotient n F)
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  exact imp_congr_right fun _ => RankinSelberg.isPairLPolynomial_congr_whittakerSets hπ hσ

/-- The symmetric L relation in either rank order depends only on the Whittaker functions
of both members for both characters. -/
theorem isPadicSymmetricLPolynomial_congr_whittakerSets
    (hπ : RankinSelberg.whittakerSet ψ r π = RankinSelberg.whittakerSet ψ r π₂)
    (hπ' : RankinSelberg.inverseWhittakerSet ψ r π = RankinSelberg.inverseWhittakerSet ψ r π₂)
    (hσ : RankinSelberg.whittakerSet ψ n σ = RankinSelberg.whittakerSet ψ n σ₂)
    (hσ' : RankinSelberg.inverseWhittakerSet ψ n σ = RankinSelberg.inverseWhittakerSet ψ n σ₂)
    {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π σ P ↔ IsPadicSymmetricLPolynomial F ψ ν π₂ σ₂ P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact isPadicPairLPolynomial_congr_whittakerSets hπ hσ'
  · exact isPadicPairLPolynomial_congr_whittakerSets hσ hπ'

end Congruence

section Product

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  {q : ℕ} (hq : IsResidueCardinality (F := F) q)

/-- JPSS 1983, (9.4), for `π × I(x)` with norm-ordered `x`, from the three premises over
`F`: `L(s, π × I(x)) = ∏_j L(s, π × χ_(x_j))`, as an identity of certified
L-polynomials. -/
theorem lPolynomial_principalSeries_eq_prod
    (hclass : GenericStandardModuleStatement.{uF, uV} F)
    (hpole : TemperedPoleBoundStatement.{uF, max uF uV, uF} F)
    (htail₁ : InducedTailLFactorAt.{uF, max uF uV, max uF uV, uF} F)
    (htail₂ : InducedTailLFactorAt.{uF, uF, uF, max uF uV} F)
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1 + 1) F) V) (hπ : IsGeneric ψ (n + 1) π)
    (x : Fin (n + 1) → ℂˣ) (hx : Monotone (fun i => ‖(x i : ℂ)‖))
    {PI : ℂ[X]} {Pi : Fin (n + 1) → ℂ[X]}
    (hPI : IsPadicSymmetricLPolynomial F ψ ν.val π (principalSeries hϖ n hq x) PI)
    (hPi : ∀ j, IsPadicSymmetricLPolynomial F ψ ν.val π
      (RankinSelberg.rankOneCharacter (character hϖ (x j))) (Pi j)) :
    PI = ∏ j, Pi j := by
  obtain ⟨d, hW, hW'⟩ := hclass ψ (n + 1) π hπ
  let η := unramifiedDatum hϖ n hq x hx
  have hd : IsPadicRankLPolynomial ψ ν.val d.standardModule η.standardModule PI := by
    have h1 := (isPadicSymmetricLPolynomial_congr_whittakerSets hW.symm hW'.symm rfl rfl).mp
      hPI
    exact (IsPadicRankLPolynomial.congr_equiv (Representation.Equiv.refl _)
      (unramifiedDatum_standardModuleEquiv hϖ n hq x hx).symm).mp h1
  let c := temperedTypeLPolynomialData ψ ν d η
  have hprod := temperedTypeLPolynomial_product hpole htail₁ htail₂ ψ ν d η hd c.block_spec
  have hcol : ∀ j, Pi j = ∏ i, c.blockPolynomial i j := by
    intro j
    have hj : IsPadicRankLPolynomial ψ ν.val d.standardModule
        (pointDatum hϖ hq (x j)).standardModule (Pi j) := by
      have h1 := (isPadicSymmetricLPolynomial_congr_whittakerSets hW.symm hW'.symm rfl rfl).mp
        (hPi j)
      exact (IsPadicRankLPolynomial.congr_equiv (Representation.Equiv.refl _)
        (pointDatum_standardModuleEquiv hϖ hq (x j)).symm).mp h1
    have hQ : ∀ i (j' : Fin (pointDatum hϖ hq (x j)).shape.length),
        IsPadicRankLPolynomial ψ ν.val (d.twistedBlock i).representation
          ((pointDatum hϖ hq (x j)).twistedBlock j').representation (c.blockPolynomial i j) :=
      fun i _ => c.block_spec i j
    have h := temperedTypeLPolynomial_product hpole htail₁ htail₂ ψ ν d
      (pointDatum hϖ hq (x j)) hj hQ
    rw [h]
    exact Finset.prod_congr rfl fun i _ => Fin.prod_univ_one _
  rw [hprod, Finset.prod_comm]
  exact Finset.prod_congr rfl fun j _ => (hcol j).symm

end Product

end Langlands.Conductor.OrderedUnramifiedTemperedType
