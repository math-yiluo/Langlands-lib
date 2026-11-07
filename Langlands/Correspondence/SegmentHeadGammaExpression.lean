import Langlands.Correspondence.SupercuspidalGammaFromFactorsProof
import Langlands.Representation.RankinSelberg.SegmentFactorStatement
import Langlands.Representation.Classification.SegmentFullJacquetAdjunction
import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor
import Langlands.Representation.RankinSelberg.PadicSymmetricLFactor
import Langlands.Representation.RankinSelberg.PadicGenericDualLFactor
import Langlands.Representation.RankinSelberg.LanglandsFactors

/-!
# Gamma factors of pairs of segment heads as epsilon-times-L-ratio expressions

A representation with an equal-rank gamma factor against itself has a nonzero
Whittaker functional; an irreducible admissible one is therefore generic. For a
generic pair, the published constructed epsilon data, L-polynomial and dual
L-polynomial give the gamma factor as `rationalGammaExpression`, and the dual
L-polynomial has constant term `1`. Segment heads are irreducible and admissible,
and the segment-head gamma formula of Henniart 2002, §2.6 supplies their
self-gamma factors.
-/

noncomputable section

open Polynomial

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An equal-rank gamma factor of a representation with itself supplies a
nonzero standard Whittaker functional, hence genericity. -/
theorem isGeneric_of_isPadicSymmetricGammaFactor_self
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hirr : Representation.IsIrreducible π)
    (hadm : letI := F.canonicalTopologicalData.topology; IsAdmissible π) {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor F ψ ν π π G) :
    letI := F.canonicalTopologicalData.topology
    Whittaker.IsGeneric ψ r π := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (r + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (r + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient r F.Carrier)
  have h : IsPairGammaFactor F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) ν π π G :=
    (isPadicSymmetricGammaFactor_of_le le_rfl).mp hG
  exact ⟨hirr, hadm, (isPairGammaFactor_self.mp h).2.1⟩

/-- For a generic pair, the constructed epsilon data `e`, L-polynomial `P` and
dual L-polynomial `D` satisfy the JPSS relations, `D(0) = 1`, and the gamma factor
is `rationalGammaExpression δ e P D`. -/
theorem exists_isPadicSymmetricGammaFactor_rationalGammaExpression
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π)
    (hσ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n σ) :
    ∃ (e : ℂˣ × ℤ) (P D : ℂ[X]), IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π σ P ∧ D.coeff 0 = 1 ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π σ
        (rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P D) := by
  let := F.canonicalNormedField
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have he := genericSymmetricEpsilonData_isPadic F ψ ν.val ν.property π σ hπ hσ
  have hP := genericSymmetricLPolynomial_isPadic F ψ ν.val π σ hπ hσ
  have hD := genericSymmetricDualLPolynomial_isPadic F ψ ν.val π σ hπ hσ
  exact ⟨_, _, _, he, hP, genericSymmetricDualLPolynomial_coeff_zero F ψ ν.val π σ hπ hσ,
    (symmetricGammaExpression.{uF, uV, uW} p F ψ ν r n π σ
      (genericSymmetricGammaConstructionInput F ψ ν.val ν.property π σ hπ hσ)
      _ _ _ he hP hD _).mpr rfl⟩

/-- The arbitrary-rank form of
`exists_isPadicSymmetricGammaFactor_rationalGammaExpression`, for irreducible
admissible representations with self-gamma factors. -/
theorem exists_isPadicRankGammaFactor_rationalGammaExpression
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (hπ : Representation.IsIrreducible π)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hσ : Representation.IsIrreducible σ)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ)
    {G G' : RationalFunctions} (hπG : IsPadicRankGammaFactor F ψ ν.val π π G)
    (hσG : IsPadicRankGammaFactor F ψ ν.val σ σ G') :
    ∃ (e : ℂˣ × ℤ) (P D : ℂ[X]), IsPadicRankEpsilonFactor F ψ ν.val π σ e ∧
      IsPadicRankLPolynomial F ψ ν.val π σ P ∧ D.coeff 0 = 1 ∧
      IsPadicRankGammaFactor F ψ ν.val π σ
        (rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P D) := by
  match n, t, π, σ, hπ, hπa, hσ, hσa, hπG, hσG with
  | _ + 1, _ + 1, π, σ, hπ, hπa, hσ, hσa, hπG, hσG =>
    exact exists_isPadicSymmetricGammaFactor_rationalGammaExpression F ψ ν π σ
      (isGeneric_of_isPadicSymmetricGammaFactor_self F ψ ν.val π hπ hπa hπG)
      (isGeneric_of_isPadicSymmetricGammaFactor_self F ψ ν.val σ hσ hσa hσG)
  | 0, _, _, _, _, _, _, _, hπG, _ => exact hπG.elim
  | _ + 1, 0, _, _, _, _, _, _, _, hσG => exact hσG.elim

/-- A segment head is irreducible and admissible. -/
theorem isIrreducible_isAdmissible_of_isSegmentHead
    {Δ : F.canonicalTopologicalData.Segment.{uV, uF}}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier)}
    (h : F.canonicalTopologicalData.IsSegmentHead Δ π) :
    letI := F.canonicalTopologicalData.topology
    Representation.IsIrreducible π.representation ∧ IsAdmissible π.representation := by
  obtain ⟨A, -, hhead⟩ := h
  obtain ⟨q, hq, -⟩ := hhead.2
  exact ⟨hhead.1, SegmentFullJacquet.isAdmissible_of_segmentQuotient F
    F.canonicalTopologicalData Δ.rank_pos A.obj A.property.2.1 π q hq⟩

/-- **Gamma factors of segment heads.** With the segment-head gamma formula of
Henniart 2002, §2.6, for segment heads `π` of `Δ` and `σ` of `Δ'` there are
epsilon data `e`, an L-polynomial `P` and a polynomial `D` with `D(0) = 1` such
that `rationalGammaExpression δ e P D` is the product of the gamma factors of the
pairs `(ν^(i+j) A, A')` of supercuspidal representatives. -/
theorem exists_segmentHead_rationalGammaExpression
    (hG : SegmentHeadGammaFactorStatement.{uF, uV, uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (Δ Δ' : F.canonicalTopologicalData.Segment.{uV, uF})
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ.degree F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear Δ'.degree F.Carrier))
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (A' : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ'.rank))
    (hπ : F.canonicalTopologicalData.IsSegmentHead Δ π)
    (hσ : F.canonicalTopologicalData.IsSegmentHead Δ' σ)
    (hA : Δ.base.IsRepresentedBy A) (hA' : Δ'.base.IsRepresentedBy A') :
    letI := F.canonicalTopologicalData.topology
    ∃ (e : ℂˣ × ℤ) (P D : ℂ[X]) (H : Fin Δ.length → Fin Δ'.length → RationalFunctions),
      IsPadicRankEpsilonFactor F ψ ν.val π.representation σ.representation e ∧
      IsPadicRankLPolynomial F ψ ν.val π.representation σ.representation P ∧
      D.coeff 0 = 1 ∧
      (∀ (i : Fin Δ.length) (j : Fin Δ'.length), IsPadicRankGammaFactor F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm Δ.rank)
          (((i : ℕ) + (j : ℕ) : ℕ) : ℝ) A.obj.representation)
        A'.obj.representation (H i j)) ∧
      rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P D = ∏ i, ∏ j, H i j := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨Gπ, -, hGπ, -, -⟩ := hG p F ψ ν Δ Δ π π A A hπ hπ hA hA
  obtain ⟨Gσ, -, hGσ, -, -⟩ := hG p F ψ ν Δ' Δ' σ σ A' A' hσ hσ hA' hA'
  obtain ⟨G, H, hGH, hH, hGprod⟩ := hG p F ψ ν Δ Δ' π σ A A' hπ hσ hA hA'
  obtain ⟨hπi, hπa⟩ := isIrreducible_isAdmissible_of_isSegmentHead F hπ
  obtain ⟨hσi, hσa⟩ := isIrreducible_isAdmissible_of_isSegmentHead F hσ
  obtain ⟨e, P, D, he, hP, hD, hγ⟩ := exists_isPadicRankGammaFactor_rationalGammaExpression F ψ ν
    π.representation σ.representation hπi hπa hσi hσa hGπ hGσ
  exact ⟨e, P, D, H, he, hP, hD, hH, (hγ.unique hGH).trans hGprod⟩

end Langlands.RankinSelberg
