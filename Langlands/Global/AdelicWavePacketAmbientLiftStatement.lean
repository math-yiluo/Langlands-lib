import Langlands.Global.AdelicParabolicSpectrum
import Langlands.Global.AdelicWavePacketCompletenessReduction

/-! # Lifting a relative wave packet by an ambient spectral coefficient -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

/-- The factor contributed by one compactly supported smooth ambient spectral coefficient.
The convention is the positive exponential of the imaginary ambient character parameter. -/
def ambientWavePacketProfile {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {m : ℕ}
    (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ)
    (g : AdelicGroupPoints F G) : ℂ :=
  ∫ z, b z * parameterPower F G (imaginaryParameter F G (eG z)) g ∂(spectralMeasure m)

/-- Multiplying a relative wave packet by a profile in ambient parameters gives a full wave
packet. The inducing forms and continuation domains can be retained. The chart `eG` and the
smooth compactly supported coefficient `b` are independent of the parabolic. -/
def WavePacketAmbientLiftStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (iU : U ⟶ P) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      {m : ℕ} (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) (b : (Fin m → ℝ) → ℂ),
    ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
    ∀ (Θ : AdelicGroupPoints F G → ℂ),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
    IsWavePacket F G K rho hsmooth hcalc (fun g => ambientWavePacketProfile eG b g * Θ g)

end Langlands.Global
