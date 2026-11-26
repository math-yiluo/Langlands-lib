import Langlands.Global.AdelicTemperedVanishingReduction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Recovering the weak constant term pairing from the packet pairing formula -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory
open scoped CategoryTheory.MonObj ContDiff Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- A smooth function on a finite-dimensional real normed space has a smooth compactly
supported representative of its germs at a finite set of points. -/
private theorem exists_compact_test_with_germs {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (S : Finset V) {b : V → ℂ}
    (hb : ContDiff ℝ ∞ b) :
    ∃ a : V → ℂ, ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
      ∀ z ∈ S, a =ᶠ[𝓝 z] b := by
  let r : ℝ := 1 + ∑ z ∈ S, ‖z‖
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let cutoff : ContDiffBump (0 : V) := ⟨r, r + 1, hr, lt_add_of_pos_right _ one_pos⟩
  refine ⟨fun z => cutoff z • b z, cutoff.contDiff.smul hb,
    cutoff.hasCompactSupport.smul_right, fun z hz => ?_⟩
  have hball : z ∈ Metric.ball (0 : V) cutoff.rIn := by
    change dist z 0 < r
    rw [dist_zero_right]
    exact (Finset.single_le_sum (fun w _ => norm_nonneg w) hz).trans_lt
      (lt_one_add _)
  filter_upwards [cutoff.eventuallyEq_one_of_mem_ball hball] with w hw
  change cutoff w = 1 at hw
  rw [hw, one_smul]

section Phase

variable {F : Type} [Field F] [NumberField F]
  {P : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}

/-- The negative Fourier phase for the split-component point `x` in real coordinates
on the inducing parameter space. -/
def weakPairingFourierPhase (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (x : AdelicGroupPoints F P) (z : Fin n → ℝ) : ℂ :=
  parameterPower F P (-imaginaryParameter F P (e z)) x

theorem contDiff_weakPairingFourierPhase
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (x : AdelicGroupPoints F P) :
    ContDiff ℝ ∞ (weakPairingFourierPhase e x) := by
  let H := characterLog F P x
  let ev : (RealCharacterDual F P →ₗ[ℝ] ℂ) →ₗ[ℝ] ℂ := LinearMap.applyₗ H
  let phase : (Fin n → ℝ) →ₗ[ℝ] ℂ :=
    - (ev.comp (((complexParameterPairing F P).restrictScalars ℝ).comp
      ((imaginaryParameter F P).comp e.toLinearMap)))
  have hphase : weakPairingFourierPhase e x = fun z => Complex.exp (phase z) := by
    funext z
    unfold weakPairingFourierPhase parameterPower
    rw [map_neg]
    rfl
  rw [hphase]
  exact phase.toContinuousLinearMap.contDiff.cexp

end Phase

/-- The limit of Delorme's distribution formula (Proposition 7.8 and the proof of
Lemma 7.11), with the central Fourier factor. The functional `L` depends on the germs
at finitely many spectral points. The derivatives on the point masses act on tests
through their formal transposes. Its value on the negative Fourier phase recovers the
normalized weak constant term pairing, and its value on a smooth compact coefficient
gives the packet pairing up to nonzero Haar normalization. -/
def WavePacketWeakConstantTermPairingFormulaStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K),
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ (Φ : AdelicGroupPoints F G → ℂ),
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
      𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
        (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ →
    ∃ (_ : IsClosedImmersion (𝓕.p J).hom.hom.left)
      (hKJ : IsIwasawaCompact (𝓕.p J) K)
      (r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J))
      (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
      (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
      (hA : IsSplitTorus (𝓕.A J).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
      (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (𝓕.P J))
      (E : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F (𝓕.P J)))
      (S : Finset (Fin n → ℝ)) (L : ((Fin n → ℝ) → ℂ) → ℂ) (C : ℂ),
      Set.range (imaginaryParameter F (𝓕.P J)) ⊆ D ∧
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) ∧
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E lam = hKJ.eisensteinSeries φ lam) ∧
      C ≠ 0 ∧
      (∀ a b, (∀ z ∈ S, a =ᶠ[𝓝 z] b) → L a = L b) ∧
      (∀ a : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ a → HasCompactSupport a →
        let Θ : AdelicGroupPoints F G → ℂ :=
          fun g => ∫ z, a z * E (imaginaryParameter F (𝓕.P J) (e z)) g ∂(spectralMeasure n)
        Integrable (fun y => Θ y.out * (starRingEnd ℂ) (Φ y.out)) μG ∧
        (∫ y, Θ y.out * (starRingEnd ℂ) (Φ y.out) ∂μG) = C * L a) ∧
      ∀ x ∈ 𝓕.positiveSplitComponent J,
        Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ ψ)
          (𝓕.squareIntegrablePairingMeasure K hK.isCompact J) ∧
        (∫ z, 𝓕.squareIntegrablePairingIntegrand K J x φ ψ z
            ∂(𝓕.squareIntegrablePairingMeasure K hK.isCompact J)) =
          parameterPower F (𝓕.P J) (modulusParameter F (𝓕.P J)) x * L (weakPairingFourierPhase e x)

/-- Cut off the negative Fourier phase near the finite set of frequencies. Orthogonality
to the resulting wave packet forces the pairing at the chosen split-component point
to vanish. -/
theorem wavePacketWeakConstantTermOrthogonality_of_pairingFormula
    (hFormula : WavePacketWeakConstantTermPairingFormulaStatement) :
    WavePacketWeakConstantTermOrthogonalityStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho 𝓕 hK μG Φ hΦ horth J ψ hψ φ hφ x hx
  obtain ⟨hpJ, hKJ, r, hi, hW, hf, hA, hT, n, e, E, D, S, L, C,
      hD, hE, hreg, hC, hlocal, hpacket, hpair⟩ :=
    hFormula F G hG K rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J ψ hψ φ hφ
  obtain ⟨hInt, hPair⟩ := hpair x hx
  refine ⟨hInt, ?_⟩
  obtain ⟨a, ha, haCompact, haGerms⟩ :=
    exists_compact_test_with_germs S (contDiff_weakPairingFourierPhase e x)
  let Θ : AdelicGroupPoints F G → ℂ :=
    fun g => ∫ z, a z * E (imaginaryParameter F (𝓕.P J) (e z)) g ∂(spectralMeasure n)
  have hΘ : IsWavePacket F G K rho hsmooth hcalc Θ := by
    refine ⟨𝓕.P J, 𝓕.M J, 𝓕.U J, 𝓕.A J, 𝓕.affineP J, 𝓕.affineM J, 𝓕.finiteTypeM J,
      𝓕.affineU J, 𝓕.p J, hpJ, 𝓕.iU J, 𝓕.l J, 𝓕.closedU J, 𝓕.a J, r, hi, hW, hf,
      hA, hT, 𝓕.isUnipotentRadical J, hKJ, n, e, 1, fun _ => φ, fun _ => a, fun _ => E,
      D, fun _ => hφ, fun _ => ⟨ha, haCompact⟩, hD, fun _ => hE, fun _ => hreg, ?_⟩
    simp only [Θ, Fin.sum_univ_one]
  obtain ⟨_, hEval⟩ := hpacket a ha haCompact
  have hZero : (∫ y, Θ y.out * (starRingEnd ℂ) (Φ y.out) ∂μG) = 0 := by
    have hConj := congrArg (starRingEnd ℂ) (horth Θ hΘ)
    rw [map_zero, ← integral_conj] at hConj
    simpa only [map_mul, starRingEnd_apply, star_star, mul_comm] using hConj
  have hLa : L a = 0 := (mul_eq_zero.mp (hEval.symm.trans hZero)).resolve_left hC
  rw [hPair, ← hlocal a _ haGerms, hLa, mul_zero]

end Langlands.Global
