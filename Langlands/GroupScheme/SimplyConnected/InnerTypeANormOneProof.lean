import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.GroupScheme.SimplyConnected.SpecialLinearInnerFormNormOneProof
import Langlands.GroupScheme.Reductive.SpecialLinearPinningProof
import Langlands.LinearAlgebra.CorootSpanCartanEquivProof
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof

/-!
# Proof of reduced-norm-one presentations of simply connected groups of inner type A

This module proves `Langlands.GroupScheme.InnerTypeANormOneStatement` by applying the
reduction `InnerTypeANormOneReduction.innerTypeANormOne_of_inputs` to the four published
input theorems.
-/

universe u

namespace Langlands.GroupScheme

/-- A simply connected absolutely almost-simple group of inner type `A_n` over an
arbitrary field is isomorphic to the reduced-norm-one group of a central simple algebra
of reduced degree `n + 1`. -/
theorem innerTypeANormOne : InnerTypeANormOneStatement.{u} :=
  InnerTypeANormOneReduction.innerTypeANormOne_of_inputs specialLinearSimplyConnectedPinning
    Langlands.LinearAlgebra.corootSpanCartanEquiv specialLinearInnerFormNormOne
    starActionFiniteStage

end Langlands.GroupScheme
