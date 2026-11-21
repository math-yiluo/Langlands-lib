import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompactHeightEnvelope
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedTemperedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedConstantTermFourier

/-! # Absolute convergence of the Fourier pairing for tempered Levi coefficients -/

noncomputable section

universe uG uV

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate ENNReal NNReal

namespace Langlands.HarishChandraSchwartz

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
  {μ : Measure G} {σ : G → ℝ} {σM : M → ℝ}

/-- The VII.1.2 double integral is absolutely convergent for tempered
inducing coefficients when the Levi height is controlled in the ambient
Iwasawa decomposition and left translation by K is bounded in height. -/
def TemperedFourierDoubleIntegrabilityStatement : Prop :=
  IsUnimodularModulus U hU →
  LeviData (K : Subgroup G) P₀ P M δ₀
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection →
  (∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) →
  Continuous σ → (∀ g, 0 ≤ σ g) → (∀ x, 0 ≤ σM x) →
  (∃ D : ℝ, 0 < D ∧ ∀ (k : K) (g : G), 1 + σ ((k : G) * g) ≤ D * (1 + σ g)) →
  LeviSigmaBound h (K : Set G) σ σM →
  HasTemperedCoefficients (xi hMK δ₀M) σM A.representation →
  L2Weights μ (xi hP₀K δ₀) σ →
  ∀ (ψ : productInducedCoefficientObject h hU A) (f : Space (xi hP₀K δ₀) σ),
    Integrable (coefficientPairingIntegrand h hU A K ψ f) (μ.prod (CompactInduction.measure K hK))

set_option maxHeartbeats 2000000 in
/-- Use the compact integrand estimate, integrate its positive Levi Xi
weight by II.1.6, and apply the ambient square-weight estimate. -/
theorem temperedFourierDoubleIntegrability :
    TemperedFourierDoubleIntegrabilityStatement h hU A K hK hP₀K hMK
      (μ := μ) (σ := σ) (σM := σM) (δ₀ := δ₀) (δ₀M := δ₀M) := by
  intro hδ hL hδ₀ hσc hσ hσM hσK hlevi hT hw ψ f
  let : Nonempty (CompactOpenSubgroup G) := ⟨⟨K, hK⟩⟩
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨B, R, hB, hR, hb⟩ := norm_inducedIntegrandKernel_le_rpow h hU A K hK
    hδ hL hP₀K hMK hσ hσM hlevi hT ψ
  obtain ⟨D, hD, hKσ⟩ := hσK
  let C := B * D ^ R
  have hC : 0 < C := mul_pos hB (Real.rpow_pos_of_pos hD _)
  let W := leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M
  have hW (g : G) : 0 ≤ W g :=
    mul_nonneg (NNReal.coe_nonneg _) (integral_nonneg fun _ => iwasawaWeight_nonneg _)
  let w (g : G) : ℝ := (1 + σ g) ^ R
  have hw0 (g : G) : 0 ≤ w g := Real.rpow_nonneg (by linarith [hσ g]) _
  have hweight (k : K) (g : G) : w ((k : G) * g) ≤ D ^ R * w g := by
    change (1 + σ ((k : G) * g)) ^ R ≤ D ^ R * (1 + σ g) ^ R
    rw [← Real.mul_rpow hD.le (by linarith [hσ g])]
    exact Real.rpow_le_rpow (by linarith [hσ ((k : G) * g)]) (hKσ k g) hR
  let a (g : G) : ℂ := (xi hP₀K δ₀ g * w g : ℝ)
  have ha0 (g : G) : 0 ≤ xi hP₀K δ₀ g * w g := mul_nonneg (hw.pos g).le (hw0 g)
  have hac : Continuous a := Complex.continuous_ofReal.comp
    ((continuous_xi hδ₀ K.isOpen).mul ((continuous_const.add hσc).rpow_const
      fun _ => Or.inr hR))
  have han : nu (xi hP₀K δ₀) σ (-R) a ≠ ⊤ := by
    apply nu_ne_top_of_norm_le hw.pos hw.nonneg (c := 1)
    intro g
    change ‖((xi hP₀K δ₀ g * w g : ℝ) : ℂ)‖ ≤ 1 * xi hP₀K δ₀ g * (1 + σ g) ^ (- -R)
    rw [Complex.norm_real, Real.norm_of_nonneg (ha0 g), one_mul, neg_neg]
  have hfin : ∫⁻ g, ‖f g * a g‖ₑ ∂μ < ⊤ := (Space.integrable_mul hw hac han f).2
  have hpt (x : G × K) : ‖coefficientPairingIntegrand h hU A K ψ f x‖ₑ ≤
      ENNReal.ofReal (C * W ((x.2 : G) * x.1)) *
        (ENNReal.ofReal (w x.1) * ‖f x.1‖ₑ) := by
    rw [coefficientPairingIntegrand, enorm_mul, RCLike.enorm_conj,
      ← inducedIntegrandKernel_mul h hU A K ψ x.2 x.1, ← ofReal_norm,
      ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hC.le (hW _))]
    gcongr
    calc ‖inducedIntegrandKernel h hU A K ψ x.2 ((x.2 : G) * x.1)‖
      ≤ B * W ((x.2 : G) * x.1) * w ((x.2 : G) * x.1) := hb x.2 _
      _ ≤ B * W ((x.2 : G) * x.1) * (D ^ R * w x.1) :=
        mul_le_mul_of_nonneg_left (hweight x.2 x.1) (mul_nonneg hB.le (hW _))
      _ = C * W ((x.2 : G) * x.1) * w x.1 := by unfold C; ring
  refine ⟨((Complex.continuous_conj.comp (continuous_integrand_uncurry h hU A K ψ)).mul
    ((Space.continuous f).comp continuous_fst)).aestronglyMeasurable, ?_⟩
  calc ∫⁻ x, ‖coefficientPairingIntegrand h hU A K ψ f x‖ₑ ∂μ.prod (CompactInduction.measure K hK)
      ≤ ∫⁻ x, ENNReal.ofReal (C * W ((x.2 : G) * x.1)) *
          (ENNReal.ofReal (w x.1) * ‖f x.1‖ₑ) ∂μ.prod (CompactInduction.measure K hK) :=
        lintegral_mono hpt
    _ ≤ ∫⁻ g, ∫⁻ k : K, ENNReal.ofReal (C * W ((k : G) * g)) *
          (ENNReal.ofReal (w g) * ‖f g‖ₑ) ∂CompactInduction.measure K hK ∂μ :=
        lintegral_prod_le _
    _ = ∫⁻ g, ENNReal.ofReal C * ‖f g * a g‖ₑ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top),
          show (∫⁻ k : K, ENNReal.ofReal (C * W ((k : G) * g)) ∂CompactInduction.measure K hK) =
              ENNReal.ofReal (C * xi hP₀K δ₀ g) from
            lintegral_leviXiWeight_mul h hU K hK hL hP₀K hMK hδ₀ hC g,
          enorm_mul, ← ofReal_norm (a g), Complex.norm_real, Real.norm_of_nonneg (ha0 g),
          ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul (hw.pos g).le]
        ring
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end Generic

section Rational

open _root_.CategoryTheory _root_.AlgebraicGeometry Langlands.GroupScheme
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type uG} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "𝐉" => RationalPointFamily.rootSet i ν I

set_option maxHeartbeats 2000000 in
/-- Actual VII.1.2 convergence for a standard parabolic under the tempered
Levi bound. The original closed matrix height may be used for any compact K. -/
theorem integrable_rationalTemperedCoefficientPairingIntegrand
    (hMK : IsIwasawaPair
      ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν 𝐉))
      (K.toSubgroup.subgroupOf (standardLeviPoints i ν 𝐉)))
    (hρ : IsClosedSubgroup ρ) (A : SmoothRep.{0, uG, uV} ℂ (standardLeviPoints i ν 𝐉))
    (hT : HasTemperedCoefficients (rationalLeviXi hKc hMK)
      (fun m => rationalHeight (F := F) ρ m) A.representation)
    {muG : Measure (rationalPoints G)}
    (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (ψ : productInducedCoefficientObject
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν 𝐉) A)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    Integrable
      (fun x : rationalPoints G × K => conj (CompactInduction.integrand
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν 𝐉) A K x.1 ψ x.2) * f x.1)
      (muG.prod (CompactInduction.measure K hKc)) := by
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
  obtain ⟨D, hD, hb⟩ := exists_rationalHeight_le_on_compact ρ K.toSubgroup hKc
  have hc : ∃ c : ℝ, 0 < c ∧ ∀ (k : K) (g : rationalPoints G),
      1 + rationalHeight (F := F) ρ ((k : rationalPoints G) * g) ≤
        c * (1 + rationalHeight (F := F) ρ g) := by
    refine ⟨1 + D, by linarith, fun k g => ?_⟩
    have hmul := rationalHeight_mul_le ρ (k : rationalPoints G) g
    have hbound := hb k
    have hn := rationalHeight_nonneg ρ g
    nlinarith [mul_nonneg hD hn]
  have hJ := RationalPointFamily.rootSet_subset i ν I
  have hint := temperedFourierDoubleIntegrability
    (isSemidirectDecomposition_standard hG hi hν hJ) (isClosed_standardUnipotentPoints i ν 𝐉)
    A K hKc hPK hMK
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν hJ K.isOpen hKc)
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)
    (continuous_rationalHeight ρ) (rationalHeight_nonneg ρ)
    (fun m => rationalHeight_nonneg ρ m) hc
    (rationalLeviSigmaBound ρ hG hi hν hJ hρ hKc) hT
    (rationalL2Weights K.isOpen hKc hPK ρ hsw) ψ f
  exact hint

end Rational

end Langlands.HarishChandraSchwartz
