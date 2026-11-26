import Langlands.Global.AdelicWavePacketCompletenessReduction
import Langlands.Global.AdelicWavePacketRationalInvariance

/-! # Left rational invariance of wave packets

Every wave packet of `IsWavePacket` (the packets of `WavePacketCompletenessStatement`) is left
invariant under the rational points `G(F)`. The continuations `E j` of the Eisenstein series are
left `G(F)`-invariant at every parameter of their common domain of holomorphy
(`eisensteinContinuation_leftRationalInvariant`), and that domain contains every imaginary
parameter at which the packet integrand is evaluated. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Wave packets of Eisenstein series are left `G(F)`-invariant: for every connected reductive
`G` and every `Θ` with `IsWavePacket F G K rho hsmooth hcalc Θ`, `Θ(γ g) = Θ(g)` for all
`γ ∈ G(F)` and `g ∈ G(𝔸)`. -/
def WavePacketLeftRationalInvarianceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (Θ : AdelicGroupPoints F G → ℂ), IsWavePacket F G K rho hsmooth hcalc Θ →
      IsLeftInvariantUnder F G (rationalSubgroup F G) Θ

theorem wavePacketLeftRationalInvariance : WavePacketLeftRationalInvarianceStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc Θ hΘ
  obtain ⟨P, M, U, A, _, _, _, _, p, _, iU, l, _, a, r, _, _, _, hA, hT, hU, hK, n, e, k, v, c,
    E, D, hv, -, himag, hE, hreg, rfl⟩ := hΘ
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  exact packetIntegral_leftRationalInvariant (spectralMeasure n) (D := D)
    (fun x => imaginaryParameter F P (e x)) c E (fun _ x _ => himag ⟨e x, rfl⟩)
    (fun j _ hlam => eisensteinContinuation_leftRationalInvariant hK (hv j).1.1 hU r hA hT hG
      (hE j) (hreg j) hlam)

end Langlands.Global
