import Langlands.Global.AdelicContinuedIntertwiningConvolution
import Langlands.Global.AdelicWavePacketTranslationReduction

/-! # Finite spans for normalized convolution at a presented parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- With the compatible Haar measure for the presented parabolic, compactly supported
left-finite convolution of a square-integrable inducing form admits a finite entire expansion
in square-integrable inducing forms. The Iwasawa hypothesis is for the given parabolic. -/
def NormalizedConvolutionFiniteSpanStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsIso (subgroupMultiplication l iU) → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ v : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v →
    ∀ kernel : AdelicGroupPoints F G → ℂ,
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) kernel →
      ∃ (m : ℕ) (u : Fin m → AdelicGroupPoints F G → ℂ)
        (b : Fin m → ComplexCharacterParameter F P → ℂ),
        (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (u j)) ∧
        IsFiniteNormalizedConvolutionExpansion hK kernel v u b

end Langlands.Global
