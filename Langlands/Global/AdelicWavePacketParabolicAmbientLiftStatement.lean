import Langlands.Global.AdelicNonAssociateWavePacketOrthogonality
import Langlands.Global.AdelicWavePacketAmbientLiftStatement

/-! # Lifting a relative wave packet to a wave packet of the same parabolic

Multiplying a wave packet of `P` over `i(𝔞_M^G)^*` (`IsRelativeWavePacket`) by the profile of a
smooth compactly supported coefficient in the ambient parameters of `G`
(`ambientWavePacketProfile`) gives a wave packet of the same presented parabolic `P` over all of
`i𝔞_P^*` (`IsParabolicWavePacket`). This is the form of the lift that the orthogonality of
non-associate parabolics on `[G]` needs; the published `WavePacketAmbientLiftStatement` has the
same hypotheses and concludes only `IsWavePacket`, in which the parabolic is quantified anew. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

/-- **Ambient lift of a relative wave packet, retaining the parabolic.** Let `G` be connected
reductive over a number field, `P = MU` a presented parabolic with geometric unipotent radical
and `P(𝔸)K = G(𝔸)`, `eG : ℝ^m ≃ X^*(G) ⊗ ℝ` linear coordinates and `b` a smooth compactly
supported coefficient on `ℝ^m`. If `Θ` is a wave packet of `P` over `i(𝔞_M^G)^*`, then
`g ↦ (∫ b(z) g^{i eG(z)} dz) · Θ(g)` is a wave packet of the same `P` over `i𝔞_P^*`
(`IsParabolicWavePacket` for the same `hK`, `iU`, `l`, `r`, `hA`, `hT`). -/
def WavePacketParabolicAmbientLiftStatement : Prop :=
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
    IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT
      (fun g => ambientWavePacketProfile eG b g * Θ g)

end Langlands.Global
