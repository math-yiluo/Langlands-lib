import Langlands.Representation.Exponents.ActualQuotientRealBlock
import Langlands.Representation.Exponents.FineHomRealBlockFactorization
import Langlands.Representation.Exponents.WholeInductionLeadingRealBlockStatement
import Langlands.Representation.Classification.RelativeCosocleHomUpperReduction
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof

/-! Relative Hom comparison from whole-induction isolation and finite generation. -/

noncomputable section

namespace Langlands.RelativeCosocleHomIsolationReduction

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison
open CuspidalJacquetMultiplicity RelativeHomComparison

universe uG uA uB uC uF uV uM uW uZ

section Algebra

variable {G : Type uG} [Group G]
  {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

private def homPrecompEquiv {ρ : Representation ℂ G A}
    {σ : Representation ℂ G B} (e : ρ.Equiv σ) (τ : Representation ℂ G C) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] σ.IntertwiningMap τ where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

-- Reused from the detection/lower-bound transport of Workers 845, 526 and 435.
private def homPostcompEquiv (ρ : Representation ℂ G A)
    {σ : Representation ℂ G B} {τ : Representation ℂ G C} (e : σ.Equiv τ) :
    ρ.IntertwiningMap σ ≃ₗ[ℂ] ρ.IntertwiningMap τ where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)

end Algebra

/-- The common coarse twist preserves the actual refined-opposite Hom space,
using the fixed induction twist equivalence and public second adjointness. -/
def fineTwistHomEquiv
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (hi : Representation.IsIrreducible ω.ρ)
    (hc : letI := T.topology; CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ)
    (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hπ : letI := T.topology; IsAdmissible π.ρ) :
    letI := T.topology
    (fineTwist T B S ω v₀ 0).ρ.IntertwiningMap
        (T.normalizedRefinedOppositeJacquet B S π.ρ) ≃ₗ[ℂ]
      (fineTwist T B S ω v₀ t).ρ.IntertwiningMap
        (T.normalizedRefinedOppositeJacquet B S (T.leviRealPowerTwist B t π.ρ)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  have hτ₀ := fineTwistIrreducibleAdmissible p F T n B S ω hi hc v₀ 0
  have hτt := fineTwistIrreducibleAdmissible p F T n B S ω hi hc v₀ t
  have hπt :=
    ((relativeCosocleAdmissibility.{uF,uW,uW} p F T n B π).2.2 hπ t).1
  let E :=
    (Parabolic.normalizedSecondAdjointness.{uF,uV,uW}.2 p F T n hn B S).choose
  exact (E _ π hτ₀.2.1 hπ).symm.trans
    ((twistIntertwiningEquiv (T.leviRealPowerCharacter B t) _ π.ρ).trans
      ((homPrecompEquiv (coarseTwistEquiv T B S ω v₀ t) _).trans
        (E _ (Rep.of (T.leviRealPowerTwist B t π.ρ)) hτt.2.1 hπt)))

/-- The actual whole-induction finite-generation family used by this reduction. -/
def TemperedInductionFiniteGenerationInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible π.ρ → IsLeviTempered T B π →
      ∀ (t : Fin B.length → ℝ), StrictAnti t →
        let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
        let X := induced T B πt
        Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) X.ρ.asModule

open scoped IsSimpleOrder in
/-- Public finite-length preservation and actual twist regularity prove the
whole-induction finite-generation family without an induced-FG premise. -/
theorem temperedInductionFiniteGeneration :
    TemperedInductionFiniteGenerationInput.{uF,uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B π hπ htemp t _ht
  let ρt := T.leviRealPowerTwist B t π.ρ
  have hρi : Representation.IsIrreducible ρt :=
    (T.isIrreducible_leviRealPowerTwist_iff B t π.ρ).mpr hπ
  let := hρi
  have hρl : IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) ρt.asModule :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hρa : IsAdmissible ρt :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr htemp.isAdmissible
  have hlength := Classification.normalizedInductionFiniteLength F T hn B ρt hρa hρl
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).1
  change Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
    (T.normalizedParabolicInduced B ρt).asModule
  exact inferInstance

-- Literal-shape transport follows Worker 435's assembly draft.
private theorem transportFineData {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} {C D : BlockShape n} (h : C = D)
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → CuspidalSupport.IsLeviCuspidal C ω.ρ →
      Representation.IsIrreducible (h ▸ ω : Rep ℂ (D.Levi F.Carrier)).ρ ∧
        CuspidalSupport.IsLeviCuspidal D (h ▸ ω : Rep ℂ (D.Levi F.Carrier)).ρ := by
  cases h
  exact fun hi hc => ⟨hi, hc⟩

set_option maxHeartbeats 1000000 in
/-- Actual whole-induction isolation and finite generation imply the upper
bound under the two stated whole-induction hypotheses. -/
theorem upperBoundOfIsolationAndFiniteGeneration
    (hisolation : Exponents.WholeInductionLeadingRealBlockStatement.{uF,uW})
    (hfg : TemperedInductionFiniteGenerationInput.{uF,uW}) :
    RelativeCosocleHomUpperReduction.UpperBoundCase.{uF,uV,uM,uW,uZ} := by
  dsimp only [RelativeCosocleHomUpperReduction.UpperBoundCase]
  intro p _ F T
  let := T.topology
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀ σ hσirr hσdisc hσquot
    π hπirr hπtemp t ht J hJirr hJquot
  obtain ⟨q, hq⟩ := hJquot
  let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
  let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
  obtain ⟨hωBirr, hωBcusp⟩ := transportFineData T h ω hωirr hωcusp
  let α := Rep.of (T.leviRealPowerTwist B t π.ρ)
  let N := oppositeJacquet T B J
  obtain ⟨i, r, _, hfix⟩ := hisolation p F T n hn B π hπirr hπtemp t ht
  obtain ⟨rQ, _, hrfix⟩ :=
    ActualQuotientRealBlock.quotientRetractionOfFiniteGeneration
      T hn B π hπirr hπtemp t (hfg p F T n hn B π hπirr hπtemp t ht)
        J hJirr q hq i r hfix
  let iQ := (ActualQuotientRealBlock.oppositeMap T B q).comp i
  have hadm := (relativeCosocleAdmissibility p F T n B π).2.2
    hπtemp.isAdmissible t
  have hJadm := hadm.2.2 J q hq
  have hNadm : IsAdmissible N.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B J.V J.ρ hJadm
  have hτt :=
    fineTwistIrreducibleAdmissible p F T n B S ωB hωBirr hωBcusp vB t
  have hinj :=
    FineHomRealBlockFactorization.nestedFineHomPostcomposeInjective
      T hn B Q R S h ω N α hωirr hωcusp.1 hωunit v₀ hv₀ t rQ iQ
        hrfix hτt.2.1 hNadm
  obtain ⟨φ, _⟩ :=
    Parabolic.normalizedOppositeRefinementTransitivity.{uF,uZ} p F T n B S J
  let EC := homPostcompEquiv (fineTwist T B S ωB vB t).ρ φ.symm
  let LP := Representation.IntertwiningMap.llcomp (fineTwist T B S ωB vB t).ρ
    (T.normalizedRefinedOppositeJacquet B S N.ρ)
    (T.normalizedRefinedOppositeJacquet B S α.ρ)
    (T.normalizedRefinedOppositeJacquetMap B S rQ)
  let L := LP.comp EC.toLinearMap
  have hL : Function.Injective L := hinj.comp EC.injective
  have hfinite :=
    (fineOppositeJacquetHomFinite.{uF,uV,uW,uZ}
      p F T n B S ωB hωBirr hωBcusp vB t).1 α hadm.1
  let := hfinite
  have hle := LinearMap.finrank_le_finrank_of_injective hL
  let Etwist := fineTwistHomEquiv T hn B S ωB hωBirr hωBcusp
    vB t π hπtemp.isAdmissible
  exact hle.trans_eq Etwist.finrank_eq.symm

/-- Conditional exact sufficiency with all five independent universes.
Neither whole-induction input is proved by this theorem. -/
theorem comparisonOfIsolationAndFiniteGeneration
    (hisolation : Exponents.WholeInductionLeadingRealBlockStatement.{uF,uW})
    (hfg : TemperedInductionFiniteGenerationInput.{uF,uW}) :
    GLRelativeCosocleHomComparisonStatement.{uF,uV,uM,uW,uZ} :=
  RelativeCosocleHomUpperReduction.comparisonOfUpperBound
    (upperBoundOfIsolationAndFiniteGeneration hisolation hfg)

end Langlands.RelativeCosocleHomIsolationReduction
