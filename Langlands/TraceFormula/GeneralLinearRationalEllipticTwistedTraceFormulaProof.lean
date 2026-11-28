import Langlands.TraceFormula.GeneralLinearRationalEllipticTwistedTraceFormulaStatement
import Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives
import Langlands.TraceFormula.GeneralLinearWeilTwistedClosedOrbitProof
import Langlands.TraceFormula.GeneralLinearWeilTwistedCompactQuotientProof
import Langlands.TraceFormula.GroupSchemeFullL2TraceClassProof
import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction
import Langlands.TraceFormula.GroupSchemeSimpleTwistedTraceFormula

/-!
# The simple twisted trace formula for `Res_{L/K} GL_n` with rational σ-elliptic support

This module proves `GeneralLinearRationalEllipticTwistedTraceFormulaStatement`. The finitely many
contributing rational twisted classes come from `twistedEllipticClassFiniteness`, applied to the
image in `GL_n(𝔸_L)` of a compact subset of `W(𝔸_K)¹` containing the support of `fOne`; the
closed orbits and compact centralizer quotients come from `generalLinearWeilTwistedClosedOrbit`
and `generalLinearWeilTwistedCompactQuotient`; the formula itself is
`groupSchemeSimpleTwistedTraceFormula`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals
open Langlands.TraceFormula.AdelicGroupAutomorphism
open Langlands.BaseChange

namespace Langlands.TraceFormula

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "τₙ" => unitGaloisAut K L GLₙ σ

set_option hygiene false in
/-- The Haar convolution `f₁ * f₂`, for the bound variables `f₁` and `f₂`. -/
local notation "convₙ" => fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂Measure.haar

section Representatives

attribute [local instance] generalLinearSimpleTwistedTraceIsAffine
  generalLinearSimpleTwistedTraceSmooth

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {σ : L ≃ₐ[K] L} {l n : ℕ}

set_option maxHeartbeats 800000 in
/-- Let `Ω` be a compact subset of `W(𝔸_K)¹` and `S` a set of rational points of `W(𝔸_K)¹`,
each twisted-conjugate under `W(𝔸_K)¹` into `Ω` and each with a σ-elliptic coordinate
`δ ∈ GL_n(L)`. Then `S` meets finitely many rational twisted classes: there are finitely many
points of `S`, pairwise not twisted-conjugate under the rational subgroup, representing every
point of `S`. -/
theorem exists_twistedClass_representatives_of_sigmaElliptic (hcyc : IsCyclicAlgebra σ l)
    (Ω : Set (normOneSubgroup K Wₙ)) (hΩ : IsCompact Ω)
    (S : Set (rationalNormOneSubgroup K Wₙ))
    (hSΩ : ∀ q ∈ S, ∃ x : normOneSubgroup K Wₙ,
      x⁻¹ * (q : normOneSubgroup K Wₙ) * normOneAut K τₙ x ∈ Ω)
    (hSell : ∀ q ∈ S, ∃ δ : GeneralLinear n L,
      cyclicWeilAdelicMap K L n ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) =
        AdelicGL.rational L n δ ∧ IsSigmaElliptic σ l δ) :
    ∃ (m : ℕ) (r : Fin m → rationalNormOneSubgroup K Wₙ), (∀ j, r j ∈ S) ∧
      (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (normOneAut K τₙ)
        (r j : normOneSubgroup K Wₙ) (r k : normOneSubgroup K Wₙ) → j = k) ∧
      ∀ q ∈ S, ∃ j, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (normOneAut K τₙ)
        (r j : normOneSubgroup K Wₙ) (q : normOneSubgroup K Wₙ) := by
  classical
  obtain ⟨E, hEΦ, htwist, -⟩ := exists_weilAdelicEquiv (K := K) (L := L) (σ := σ) (n := n)
  have hΦc : Continuous (cyclicWeilAdelicMap K L n) := by
    have h : (cyclicWeilAdelicMap K L n) = E := funext fun g => (hEΦ g).symm
    rw [h]
    exact E.continuous
  let Ωa : Set (AdelicGL L n) :=
    cyclicWeilAdelicMap K L n '' (Subtype.val '' Ω)
  have hΩa : IsCompact Ωa := (hΩ.image continuous_subtype_val).image hΦc
  obtain ⟨R, -, hR⟩ := twistedEllipticClassFiniteness K L σ l hcyc n Ωa hΩa
  have key : ∀ q ∈ S, ∃ ρ ∈ R, ∃ δ y : GeneralLinear n L,
      cyclicWeilAdelicMap K L n ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) =
        AdelicGL.rational L n δ ∧ y⁻¹ * δ * entrywiseAut σ n y = ρ := by
    intro q hq
    obtain ⟨δ, hqδ, hδ⟩ := hSell q hq
    obtain ⟨x, hx⟩ := hSΩ q hq
    have hmeets : ∃ x' : AdelicGL L n,
        x'⁻¹ * AdelicGL.rational L n δ * AdelicGLTransport.adelicEquiv n (σ : L ≃+* L) x' ∈
          Ωa := by
      refine ⟨cyclicWeilAdelicMap K L n x.val, _, ⟨_, hx, rfl⟩, ?_⟩
      change cyclicWeilAdelicMap K L n ((x : AdelicGroupPoints K Wₙ)⁻¹ *
        ((q : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
          adelicAut K τₙ (x : AdelicGroupPoints K Wₙ)) = _
      rw [← hEΦ, map_mul, map_mul, map_inv, hEΦ, hEΦ, hEΦ, htwist, hqδ]
    obtain ⟨ρ, hρ, y, hy⟩ := hR δ hδ hmeets
    exact ⟨ρ, hρ, δ, y, hqδ, hy⟩
  choose! ρ hρR δ y hqδ hy using key
  exact exists_twistedClass_representatives _ _ S ρ
    (R : Set (GeneralLinear n L)) R.finite_toSet hρR (by
      intro q hq q' hq' hqq'
      refine isTwistedConjugate_of_rational_coordinates q q' (δ q) (δ q')
        (y q * (y q')⁻¹) (hqδ q hq) (hqδ q' hq') ?_
      have e1 := hy q hq
      have e2 := hy q' hq'
      rw [hqq'] at e1
      calc (y q * (y q')⁻¹)⁻¹ * δ q * entrywiseAut σ n (y q * (y q')⁻¹)
          = y q' * ((y q)⁻¹ * δ q * entrywiseAut σ n (y q)) *
              (entrywiseAut σ n (y q'))⁻¹ := by
            rw [map_mul, map_inv]
            group
        _ = δ q' := by
            rw [e1, ← e2]
            group)

end Representatives

-- Keep the adelic group and its subgroup constructions opaque during elaboration.
attribute [local irreducible] Global.AdelicGroupPoints.normOneSubgroup
  Global.AdelicGroupPoints.rationalNormOneSubgroup
  AdelicGroupAutomorphism.normOneAut AdelicGroupAutomorphism.unitGaloisAut twistedCentralizer
  GroupScheme.AffineWeil.corepresentableBy GroupScheme.AffineWeil.tensorFunctor
  Global.AdelicGroupPoints.topologicalSpace

attribute [local instance] generalLinearRationalEllipticTwistedTraceIsAffine
  generalLinearRationalEllipticTwistedTraceSmooth

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- The simple twisted trace formula for `Res_{L/K} GL_n` and a cyclic extension `L/K`, when
every contributing rational point is rationally σ-elliptic. -/
theorem generalLinearRationalEllipticTwistedTraceFormula :
    GeneralLinearRationalEllipticTwistedTraceFormulaStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hcyc n hPD hG T i hi _ I _ e hc _ hfix
  dsimp only
  intro f₁ f₂ hHS₁ hHS₂ hvan hrat
  -- trace class of `R(f)` and the formula on `L²([W])` for the convolution `f`
  obtain ⟨h, htr⟩ := groupSchemeFullL2TraceClass K _ hPD hG T i hi I e hc f₁ f₂ hHS₁ hHS₂ hvan
  have hcf := Langlands.Analysis.continuous_convolution_compactlySupported
    (Measure.haar : Measure (AdelicGroupPoints K Wₙ)) f₁ f₂
  have hcs := Langlands.Analysis.hasCompactSupport_convolution_compactlySupported
    (Measure.haar : Measure (AdelicGroupPoints K Wₙ)) f₁ f₂
  obtain ⟨hΘ, hΘμ, hformula⟩ := groupSchemeSimpleTwistedTraceFormula K Wₙ T i hi I e hc τₙ
    (isOfFinOrder_unitGaloisAut K L _ σ) hfix
  -- a contributing point is twisted-conjugate into the norm-one projection of the support
  let Ω : Set (normOneSubgroup K Wₙ) := normOneFactor K _ T i hi I e '' tsupport convₙ
  have hΩ : IsCompact Ω := hcs.isCompact.image (continuous_normOneFactor K _ T i hi I e)
  have hmeet : ∀ q : normOneSubgroup K Wₙ, (∃ x : normOneSubgroup K Wₙ,
      ∫ a, convₙ (positivePointMap K _ T i a *
        ((x⁻¹ * q * normOneAut K τₙ x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ))
          ∂normalizedPositiveHaarMeasure K _ T i hi I e hc ≠ 0) →
      ∃ x : normOneSubgroup K Wₙ, x⁻¹ * q * normOneAut K τₙ x ∈ Ω := by
    rintro q ⟨x, hx⟩
    refine ⟨x, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a, convₙ (positivePointMap K _ T i a *
        ((x⁻¹ * q * normOneAut K τₙ x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)) ≠ 0 := by
      by_contra! hne
      exact hx (by simp only [hne, integral_zero])
    refine ⟨_, subset_tsupport _ ha, ?_⟩
    apply Subtype.ext
    change (positivePointMap K _ T i (positiveFactor K _ T i hi I e _))⁻¹ * _ = _
    rw [positiveFactor_mul_normOne, inv_mul_cancel_left]
  -- representatives of the contributing rational twisted classes
  obtain ⟨m, r, hrS, hpair, hcover⟩ := exists_twistedClass_representatives_of_sigmaElliptic hcyc
    Ω hΩ {q | ∃ x : normOneSubgroup K Wₙ,
      ∫ a, convₙ (positivePointMap K _ T i a *
        ((x⁻¹ * (q : normOneSubgroup K Wₙ) * normOneAut K τₙ x : normOneSubgroup K Wₙ) :
          AdelicGroupPoints K Wₙ))
          ∂normalizedPositiveHaarMeasure K _ T i hi I e hc ≠ 0}
    (fun q hq => hmeet q hq) (fun q hq => hrat q q.property hq)
  -- closed twisted orbits and compact centralizer quotients of the representatives
  have hσ := fun j => hrat (r j) (r j).property (hrS j)
  choose δ hδr hδ using hσ
  have hclosed := fun j =>
    generalLinearWeilTwistedClosedOrbit K L σ l hcyc n (r j) (δ j) (hδr j) (hδ j)
  have hcompact := fun j =>
    generalLinearWeilTwistedCompactQuotient K L σ l hcyc n (r j) (δ j) (hδr j) (hδ j)
  have hcover' : ∀ q ∈ rationalNormOneSubgroup K Wₙ, (∃ x : normOneSubgroup K Wₙ,
      ∫ a, convₙ (positivePointMap K _ T i a *
        ((x⁻¹ * q * normOneAut K τₙ x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ))
          ∂normalizedPositiveHaarMeasure K _ T i hi I e hc ≠ 0) →
      ∃ j, IsTwistedConjugate (rationalNormOneSubgroup K Wₙ) (normOneAut K τₙ)
        (r j : normOneSubgroup K Wₙ) q :=
    fun q hq hx => hcover ⟨q, hq⟩ hx
  have hF := hformula convₙ hcf hcs h htr m r hclosed hcompact hpair
  dsimp only at hF
  refine ⟨hΘ, hΘμ, h, htr, m, r, hpair, fun j => ⟨hrS j, hrat (r j) (r j).property (hrS j)⟩,
    hcover', ?_⟩
  with_reducible exact hF hcover'

end Langlands.TraceFormula
