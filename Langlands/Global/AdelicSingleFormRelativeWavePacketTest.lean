import Langlands.Global.AdelicRelativeWavePacketTestedForm
import Langlands.Global.AdelicRelativeWavePacketDescentProof
import Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof
import Langlands.Global.AdelicEisensteinRegularParameterProof
import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.AdelicLocalFinitenessChamberCoordinates

/-! # Relative tests by packets with one inducing form -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ContDiff

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

section SingleForm

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The one-inducing-form standard-parabolic packets used to test the weak terms. -/
def StandardParabolicFamily.IsSingleFormWavePacket (fam : StandardParabolicFamily F G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (Θ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ (J : StandardIndex F G fam.i fam.ν) (_ : IsClosedImmersion (fam.p J).hom.hom.left)
    (hKJ : IsIwasawaCompact (fam.p J) K)
    (r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
    (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
    (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (hA : IsSplitTorus (fam.A J).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (φ : AdelicGroupPoints F G → ℂ) (n : ℕ)
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (fam.P J)) (c : (Fin n → ℝ) → ℂ)
    (E : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F (fam.P J))),
    IsSquareIntegrableInducedForm K hKJ.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ ∧
    ContDiff ℝ (⊤ : ℕ∞) c ∧ HasCompactSupport c ∧
    Set.range (imaginaryParameter F (fam.P J)) ⊆ D ∧
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) ∧
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKJ.eisensteinSeries φ lam) ∧
    Θ = fun g => ∫ z, c z * E (imaginaryParameter F (fam.P J) (e z)) g ∂(spectralMeasure n)

end SingleForm

/-- For one inducing form, orthogonality to the one-form full packets of the standard family
suffices for absolute convergence and vanishing of the relative test on the norm-one quotient.
The full packets are assumed to have the stated weighted decay. -/
def RelativeWavePacketSingleFormTestStatement : Prop :=
  WavePacketRapidDecayStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G))
    (_hK : IsIwasawaCompact (fam.p fam.bot) K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
  IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ Φ : AdelicGroupPoints F G → ℂ,
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    (∀ Ψ, fam.IsSingleFormWavePacket K rho hsmooth hcalc Ψ →
      ∫ q : RationalQuotient F G, Φ q.out * starRingEnd ℂ (Ψ q.out)
        ∂(rationalQuotientHaarMeasure F G) = 0) →
    ∀ (J : StandardIndex F G fam.i fam.ν) (_ : IsClosedImmersion (fam.p J).hom.hom.left)
    (hKJ : IsIwasawaCompact (fam.p J) K)
    (r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
    (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
    (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (hA : IsSplitTorus (fam.A J).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (φ : AdelicGroupPoints F G → ℂ) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) (fam.p J)) (c : (Fin n → ℝ) → ℂ)
    (E : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F (fam.P J))),
    IsSquareIntegrableInducedForm K hKJ.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ →
    ContDiff ℝ (⊤ : ℕ∞) c → HasCompactSupport c →
    Set.range (imaginaryParameter F (fam.P J)) ⊆ D →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKJ.eisensteinSeries φ lam) →
    let Θ (g : AdelicGroupPoints F G) :=
      ∫ z, c z * E (imaginaryParameter F (fam.P J) (e z).val) g ∂(spectralMeasure n)
    let pairing (q : NormOneRationalQuotient F G) :=
      Θ (q.out : normOneSubgroup F G).val * starRingEnd ℂ (Φ (q.out : normOneSubgroup F G).val)
    Integrable pairing (normOneRationalQuotientHaarMeasure F G) ∧
    ∫ q, pairing q ∂(normOneRationalQuotientHaarMeasure F G) = 0

theorem relativeWavePacketSingleFormTest : RelativeWavePacketSingleFormTestStatement := by
  intro hDecay F _ _ G _ _ _ fam K hK N d rho hsmooth hcalc hmax hclosed Φ hΦ horth
    J hp hKJ r hi hw hf hA hT φ n e c E D hφ hc hcpt hD hE hreg Θ pairing
  let hG := fam.connectedReductive
  let P := fam.P J
  let M := fam.M J
  let U := fam.U J
  have hU := fam.isUnipotentRadical J
  have hΘ : IsRelativeWavePacket hKJ rho hsmooth hcalc (fam.iU J) (fam.l J) r hA hT Θ := by
    refine ⟨n, e, 1, fun _ => φ, fun _ => c, fun _ => E, D, fun _ => hφ,
      fun _ => ⟨hc, hcpt⟩, hD, fun _ => hE, fun _ => hreg, ?_⟩
    simp only [Fin.sum_univ_one, Θ]
  have hDesc := relativeWavePacketDescent F G P M U (fam.A J) (fam.p J) (fam.iU J)
    (fam.l J) (fam.a J) r hA hT hG hU K hKJ rho hsmooth hcalc Θ hΘ
  obtain ⟨T₀, j, hSetup⟩ := AdelicSiegelFactors.exists_siegelAlgebraicSetup_of_generic
    F fam.i fam.ν hG fam.maximalSplit fam.generic
  let P₀ := Standard.parabolicScheme fam.i fam.ν ∅
  let p₀ := Standard.parabolicHom fam.i fam.ν ∅
  have hMin : IsMinimalParabolicSubgroup p₀ := hSetup.2.2.1
  let : IsClosedImmersion p₀.hom.hom.left := hMin.isParabolicSubgroup.isClosedSubgroup
  let : IsAffine P₀.X.left := isAffine_of_isAffineHom p₀.hom.hom.left
  refine relativePairing_of_lifted_tests hG K rho hsmooth hcalc Φ Θ hΦ hDesc.1
    (hDecay F G hG K rho hsmooth hcalc hmax hclosed
      ⟨P₀, inferInstance, p₀, inferInstance, hMin, fam.isIwasawaCompact_standardBot hK⟩)
    fun {m} eG b hb hbpt => ?_
  let e' := (spectralCoordinateProduct n m).symm.trans
    ((e.prodCongr eG).trans (relativeAmbientParameterEquiv r hG))
  let c' := spectralProductCoefficient c b
  have hc' := hc.spectralProductCoefficient hb
  have hcpt' := hcpt.spectralProductCoefficient hbpt
  have heq := relativeWavePacketAmbientLiftPresentation eisensteinRegularParameter r hA hT hG
    hKJ e eG b (fun _ : Fin 1 => c) (fun _ => φ) (fun _ => E) D hD (fun _ => hE) (fun _ => hreg)
  have heq' : (fun g => ambientWavePacketProfile eG b g * Θ g) =
      fun g => ∫ z, c' z * E (imaginaryParameter F P (e' z)) g ∂(spectralMeasure (n + m)) := by
    simpa only [Fin.sum_univ_one, c', e', Θ] using heq.symm
  have hsingle : fam.IsSingleFormWavePacket K rho hsmooth hcalc
      (fun g => ambientWavePacketProfile eG b g * Θ g) :=
    ⟨J, hp, hKJ, r, hi, hw, hf, hA, hT, φ, n + m, e', c', E, D,
      hφ, hc', hcpt', hD, hE, hreg, heq'⟩
  refine ⟨?_, horth _ hsingle⟩
  refine isWavePacket_of_isParabolicWavePacket (l := fam.l J) (r := r)
    (hA := hA) (hT := hT) hU hKJ ?_
  refine ⟨n + m, e', 1, fun _ => φ, fun _ => c', fun _ => E, D, fun _ => hφ,
    fun _ => ⟨hc', hcpt'⟩, hD, fun _ => hE, fun _ => hreg, ?_⟩
  simpa only [Fin.sum_univ_one] using heq'

end Langlands.Global
