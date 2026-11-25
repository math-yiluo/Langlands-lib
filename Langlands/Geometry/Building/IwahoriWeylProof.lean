import Langlands.Geometry.Building.IwahoriWeylStatement
import Langlands.Geometry.Building.IwahoriWeylExactSequenceReduction
import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylProof
import Langlands.Geometry.Building.KPCoverImageReduction
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterProof
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.Geometry.Building.AffineChamberTransitivity

/-! # The Iwahori–Weyl exact sequence and its chamber splitting: proofs -/

universe u

namespace Langlands.Geometry.Building

/-- **The Iwahori–Weyl exact sequence** (Kaletha–Prasad, Theorem 7.8.1(1)). Under the
apartment axioms, `Z(F)^0` is normal in `N(F)` and `G(F)^0` in `G(F)`, the action on the
apartment identifies `(N(F) ∩ G(F)^0)/Z(F)^0` with `W(Ψ)`, and this subgroup is the kernel of
the surjection `W̃^0 → G(F)/G(F)^0`. -/
theorem iwahoriWeylExactSequence : IwahoriWeylExactSequenceStatement.{u} :=
  iwahoriWeylExactSequenceStatement_of_prerequisites unramifiedZeroPointsIndependence
    Langlands.GroupScheme.simplyConnectedCentralizerProduct simplyConnectedNormalizerAffineWeyl
    (fun _ _ _ _ _ _ _ _ _ _ E => E.centralizerZeroIntersection_of_inputs
      Langlands.GroupScheme.cocenterQuotientExistence
      Langlands.GroupScheme.splitTorusCentralizerCocenterInduced inducedTorusIwahori
      Langlands.GroupScheme.splitTorusCentralizerCoverPreimage
      Langlands.GroupScheme.isSimplyConnectedFieldExtension)

/-- **The chamber splitting of the Iwahori–Weyl group** (Kaletha–Prasad 7.8.2). Under the
apartment axioms, for every chamber `C`, `W̃^0 = W_aff ⋊ W̃^0_C` and `W̃^0_C → G(F)/G(F)^0` is
bijective. -/
theorem iwahoriWeylChamberSplitting : IwahoriWeylChamberSplittingStatement.{u} :=
  iwahoriWeylChamberSplittingStatement_of_exactSequence iwahoriWeylExactSequence
    affineChamberSimpleTransitivity

end Langlands.Geometry.Building
