import Langlands.BaseChange.CharacterFunction
import Langlands.Group.GL.CentralQuotientMeasure
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Hecke.NormalQuotientBalance
import Mathlib.MeasureTheory.Integral.Prod

/-! # The character integral and the compressed coefficient trace -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis HarishChandraSchwartz JacquetLanglands

universe u uV uW

section Distribution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

private theorem traceCoefficient_eq_integral_translate (hρ : IsAdmissible ρ)
    {Θ : G → ℂ} (hΘ : IsCharacterFunction ρ hρ Θ) (H : CompactOpenSubgroup G) (g : G) :
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    ∀ (ν : Measure G) [ν.IsHaarMeasure] [ν.IsMulRightInvariant],
      traceCoefficient ρ hρ.1 H g =
        ∫ k, (Hecke.HeckeAlgebra.normalizedIndicator ν H.1 H.2 : SchwartzBruhat G) k *
          Θ (g * k) ∂ν := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro ν _ _
  let ε : SchwartzBruhat G := Hecke.HeckeAlgebra.normalizedIndicator ν H.1 H.2
  let f := Hecke.TestFunction.leftTranslate g ε
  let S := fixedVectors ρ H.toSubgroup
  have : FiniteDimensional ℂ S := hρ.2 H.1
  let p := averageProjection ρ hρ.1 H
  let j := (ρ g).comp S.subtype
  have hfactor : (Character.finiteRankIntegratedAction ν ρ hρ f).val = j.comp p := by
    rw [Character.finiteRankIntegratedAction_coe]
    ext v
    change Hecke.integratedAction ν ρ hρ.1 (Hecke.TestFunction.leftTranslate g ε) v =
      ρ g (S.subtype (p v))
    rw [Hecke.integratedAction_leftTranslate]
    change ρ g (Hecke.heckeAction ν ρ hρ.1
      (Hecke.HeckeAlgebra.normalizedIndicator ν H.1 H.2) v) = _
    rw [heckeAction_normalizedIndicator_eq_subtype_comp]
    rfl
  have htrace : Character.distribution ν ρ hρ f = traceCoefficient ρ hρ.1 H g := by
    rw [Character.distribution_apply, FiniteRankEnd.trace_eq_of_factorization _ p j hfactor]
    rfl
  rw [← htrace, (hΘ ν).2 f]
  calc
    (∫ x, f x * Θ x ∂ν) = ∫ k, f (g * k) * Θ (g * k) ∂ν :=
      (integral_mul_left_eq_self (fun x => f x * Θ x) g).symm
    _ = _ := by
      simp only [f, Hecke.TestFunction.leftTranslate_apply, inv_mul_cancel_left]
      rfl

end Distribution

section CentralQuotient

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  LocalFieldTopology.generalLinear_nonarchimedean

/-- For an integrable character times a conjugate coefficient on the central quotient,
the integral agrees with the pairing against the compressed trace for any compact open
subgroup fixing the coefficient vector. -/
def CoefficientCharacterAveragingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    let G := GeneralLinear n F
    let Q := G ⧸ Subgroup.center G
    letI := centralQuotientMeasurableSpace F n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
      (hρ : IsAdmissible ρ) {Θ : G → ℂ}, IsCharacterFunction ρ hρ Θ →
      ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G W}
        {v : W} (ℓ : SmoothDual π) (H : CompactOpenSubgroup G), v ∈ fixedVectors π H.toSubgroup →
      ∀ (μ : Measure Q) [μ.IsHaarMeasure] (Ψ T : Q → ℂ),
        (∀ g : G, Ψ (QuotientGroup.mk g) = Θ g * star (ℓ.val (π g v))) →
        Integrable Ψ μ →
        (∀ g : G, T (QuotientGroup.mk g) =
          traceCoefficient ρ hρ.1 H g * star (ℓ.val (π g v))) →
        (∫ q, Ψ q ∂μ) = ∫ q, T q ∂μ

/-- Normalized compact-open averaging compares the character product to the trace product. -/
theorem integral_character_mul_star_coefficient_eq_integral_traceCoefficient :
    CoefficientCharacterAveragingStatement.{u, uV, uW} := by
  intro F _ _ _ _ n hn G Q V _ _ ρ hρ Θ hΘ W _ _ π v ℓ H hv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let G₁ := GeneralLinear (m + 1) F
  let Z₁ := Subgroup.center G₁
  let Q₁ := G₁ ⧸ Z₁
  let _ : MeasurableSpace Q₁ := centralQuotientMeasurableSpace F (m + 1)
  have _ : BorelSpace Q₁ := centralQuotientBorelSpace F (m + 1)
  intro μ _ Ψ T hΨ hInt hT
  have : IsClosed (Z₁ : Set G₁) := by
    rw [Subgroup.coe_center, ← Set.centralizer_univ]
    exact Set.isClosed_centralizer _
  have : μ.IsMulRightInvariant := GeneralLinear.haar_centralQuotient_isMulRightInvariant μ
  let _ : MeasurableSpace G₁ := borel G₁
  have _ : BorelSpace G₁ := ⟨rfl⟩
  let ν : Measure G₁ := RankinSelberg.generalLinearHaar F m
  have : ν.IsHaarMeasure := RankinSelberg.generalLinearHaar_isHaar F m
  have : ν.IsMulRightInvariant := RankinSelberg.generalLinearHaarRightInvariant F m
  let ε : SchwartzBruhat G₁ := Hecke.HeckeAlgebra.normalizedIndicator ν H.1 H.2
  have hright (q : Q₁) : T q = ∫ k, ε k * Ψ (q * QuotientGroup.mk k) ∂ν := by
    induction q using Quotient.inductionOn with
    | _ g =>
      change T (QuotientGroup.mk g) = _
      rw [hT, traceCoefficient_eq_integral_translate hρ hΘ H g ν, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      change ε k * Θ (g * k) * star (ℓ.val (π g v)) =
        ε k * Ψ ((QuotientGroup.mk g : Q₁) * QuotientGroup.mk k)
      rw [← QuotientGroup.mk_mul, hΨ]
      by_cases hk : k ∈ H.toSubgroup
      · have hkfix : π k v = v := hv ⟨k, hk⟩
        rw [map_mul, Module.End.mul_apply, hkfix, mul_assoc]
      · have hzero : ε k = 0 := by
          have hk' : k ∉ (H.1 : Set G₁) := hk
          change Hecke.HeckeAlgebra.normalizedIndicator ν H.1 H.2 k = 0
          rw [Hecke.HeckeAlgebra.normalizedIndicator_apply, Set.indicator_of_notMem hk', mul_zero]
        simp only [hzero, zero_mul]
  have hmk : Measurable (QuotientGroup.mk : G₁ → Q₁) := QuotientGroup.continuous_mk.measurable
  have hpres : MeasurePreserving (fun p : G₁ × Q₁ => (p.1, p.2 * QuotientGroup.mk p.1))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (measurable_snd.mul (hmk.comp measurable_fst))
      (Filter.Eventually.of_forall fun k => map_mul_right_eq_self μ (QuotientGroup.mk k))
  have hε : Integrable ε ν := ε.continuous.integrable_of_hasCompactSupport ε.hasCompactSupport
  have hprod : Integrable (fun p : G₁ × Q₁ => ε p.1 * Ψ (p.2 * QuotientGroup.mk p.1))
      (ν.prod μ) := hpres.integrable_comp_of_integrable (hε.mul_prod hInt)
  have hmass : (∫ k, ε k ∂ν) = 1 := Hecke.Homomorphism.integral_normalizedIndicator ν H.1 H.2
  symm
  calc
    (∫ q, T q ∂μ) = ∫ q, ∫ k, ε k * Ψ (q * QuotientGroup.mk k) ∂ν ∂μ := by
      simp only [hright]
    _ = ∫ k, ∫ q, ε k * Ψ (q * QuotientGroup.mk k) ∂μ ∂ν :=
      (integral_integral_swap hprod).symm
    _ = ∫ k, ε k * (∫ q, Ψ q ∂μ) ∂ν := by
      simp only [integral_const_mul, integral_mul_right_eq_self]
    _ = ∫ q, Ψ q ∂μ := by rw [integral_mul_const, hmass, one_mul]

end CentralQuotient

end Langlands.BaseChange
