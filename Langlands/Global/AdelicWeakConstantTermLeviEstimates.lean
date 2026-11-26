import Langlands.Global.AdelicWeakConstantTermComponentExtraction
import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction

/-! # Weighted Levi estimates for the pairing with the weak constant term

Delorme 2023, §3.4: the absolute convergence of (3.7) for the weak constant term follows from
two estimates on `K × M(F) \ M(𝔸)^1`, with the logarithmic height `σ_{[M]}` of the Levi
quotient as weight:

* `SquareIntegrableInducedFormLeviSchwartzStatement`: every `φ ∈ A^2_P` satisfies
  `φ σ_{[M]}^n ∈ L²` for every `n` (the inclusion `A^2 ⊂ C` of Mœglin–Waldspurger I.4.1 and
  I.4.11, applied to the Levi subgroup);
* `WeakConstantTermLeviTemperedStatement`: every weak constant term `ψ = Φ_P^w` of a
  log-square-integrable automorphic form satisfies `ψ(x ·) σ_{[M]}^{-n} ∈ L²` for some `n`, at
  every point `x` of the positive split component (Delorme, Proposition 3.5 and Lemma 3.8 (ii)).

Both are stated and not proved here. `weakConstantTermPairingIntegrable_of_leviEstimates`
derives `WeakConstantTermPairingIntegrableStatement` from them by the Cauchy–Schwarz
inequality, and `weakConstantTermComponentPairingIntegrable_of_leviEstimates` derives
`WeakConstantTermComponentPairingIntegrableStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- **Weighted Schwartz estimate for `A^2_P` on the Levi quotient** (Delorme 2023, §3.4, from
Mœglin–Waldspurger I.4.1 and I.4.11 for the Levi subgroup, with (2.10)). For a compatible family
of standard parabolics whose minimal member satisfies `P_∅(𝔸) K = G(𝔸)`, every `φ ∈ A^2_P` for
`K` (`IsSquareIntegrableInducedForm`) and every `n`, the function
`(k, m) ↦ φ(m k) σ_{[M]}(m)^n` is square integrable on `K × M(F) \ M(𝔸)^1` for the pairing
measure. Here `σ_{[M]} = rationalLogHeight` of `M` for the matrix embedding `rho` restricted
along `M → P → G`, evaluated at the image of `m` in `M(F) \ M(𝔸)`. -/
def SquareIntegrableInducedFormLeviSchwartzStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
      (J : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ),
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ →
    ∀ n : ℕ,
      MemLp (fun z : K × NormOneRationalQuotient F (𝓕.M J) =>
          φ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
              ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
            (z.1 : AdelicGroupPoints F G)) *
          ((rationalLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J))
            (normOneQuotientInclusion F (𝓕.M J) z.2) : ℝ) : ℂ) ^ n)
        2 (𝓕.squareIntegrablePairingMeasure K hK.isCompact J)

/-- **Weighted temperedness of the weak constant term on the Levi quotient** (Delorme 2023,
Proposition 3.5 and Lemma 3.8 (ii), with (2.10) for the Levi subgroup). For a
log-square-integrable automorphic form `Φ`, a weak constant term `ψ = Φ_P^w` along `P = P_J`
and a point `x` of the positive split component, there is `n` such that
`(k, m) ↦ ψ(x m k) σ_{[M]}(m)^{-n}` is square integrable on `K × M(F) \ M(𝔸)^1` for the pairing
measure, with the weight of `SquareIntegrableInducedFormLeviSchwartzStatement`. -/
def WeakConstantTermLeviTemperedStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
    𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
    ∀ x ∈ 𝓕.positiveSplitComponent J, ∃ n : ℕ,
      MemLp (fun z : K × NormOneRationalQuotient F (𝓕.M J) =>
          ψ (map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
              ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
            (z.1 : AdelicGroupPoints F G)) /
          ((rationalLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J))
            (normOneQuotientInclusion F (𝓕.M J) z.2) : ℝ) : ℂ) ^ n)
        2 (𝓕.squareIntegrablePairingMeasure K hK.isCompact J)

/-- The two weighted estimates give the absolute convergence of the pairing with the weak
constant term, by the Cauchy–Schwarz inequality. -/
theorem weakConstantTermPairingIntegrable_of_leviEstimates
    (hS : SquareIntegrableInducedFormLeviSchwartzStatement)
    (hT : WeakConstantTermLeviTemperedStatement) :
    WeakConstantTermPairingIntegrableStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J ψ hψ φ hφ x hx
  obtain ⟨n, hg⟩ := hT F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J ψ hψ x hx
  have hf := hS F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK J φ hφ n
  have hint := hf.integrable_mul hg.star
  refine (hint.const_mul (𝓕.halfModulus J x)).congr (Eventually.of_forall fun z => ?_)
  set σ : ℝ := rationalLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J))
    (normOneQuotientInclusion F (𝓕.M J) z.2) with hσ
  set y := map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
      ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
    (z.1 : AdelicGroupPoints F G) with hy
  have hσ0 : ((σ : ℂ)) ^ n ≠ 0 := by
    have : (1 : ℝ) ≤ σ := one_le_rationalLogHeight _ _
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by linarith))
  have hpt : map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
      ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
      (z.1 : AdelicGroupPoints F G) = map F (𝓕.P J) G (𝓕.p J) x * y := by
    rw [hy, mul_assoc]
  simp only [Pi.mul_apply, Pi.star_apply, StandardParabolicFamily.squareIntegrablePairingIntegrand]
  rw [← hσ, ← hy, hpt, 𝓕.splitComponentEquivariant_apply J hφ.2.1 hx, star_div₀, star_pow,
    Complex.star_def, Complex.conj_ofReal]
  field_simp

/-- The two weighted estimates give the absolute convergence of the pairing with each unitary
component of a constant-term decomposition. -/
theorem weakConstantTermComponentPairingIntegrable_of_leviEstimates
    (hS : SquareIntegrableInducedFormLeviSchwartzStatement)
    (hT : WeakConstantTermLeviTemperedStatement) :
    WeakConstantTermComponentPairingIntegrableStatement :=
  weakConstantTermComponentPairingIntegrable_of_weakConstantTerm
    (weakConstantTermPairingIntegrable_of_leviEstimates hS hT)

end Langlands.Global
