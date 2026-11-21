import Langlands.Global.AdelicParabolicSpectrum

/-! # Descent of relative wave packets to the reductive quotient -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

/-- A relative wave packet on the actual adelic points is left invariant under
`A_G G(F)`. Its evaluation using the canonical quotient's representatives therefore
recovers the packet at every adelic point. -/
def RelativeWavePacketDescentStatement : Prop :=
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
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (Θ : AdelicGroupPoints F G → ℂ),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
    IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalRationalSubgroup F G) Θ ∧
      ∀ g, Θ (LeftCosetSpace.mk (RestrictionSplitCentre.canonicalRationalSubgroup F G) g).out = Θ g

end Langlands.Global
