import Langlands.Global.AdelicSpringerCentralCompactness
import Langlands.Global.AdelicGaloisBorelTwistingProof
import Langlands.Global.AdelicSplitSiegelOverlapProof
import Langlands.Global.AdelicSplitFundamentalSetFromCover
import Langlands.Global.AdelicGaloisTwistSubgroupProof

/-! # Springer's compactness theorem for a central maximal split torus -/

universe u

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.Global.AdelicGaloisUnit

/-- Springer's compactness theorem, conditional only on Lemma S (the Galois twist preserves
norm-one points and carries norm-one points of matching closed subgroups to conjugates). -/
theorem centralSplitCompactQuotient_of_galoisTwist
    (hS1 : GaloisTwistNormOneStatement.{u}) (hS2 : GaloisTwistSubgroupStatement.{u}) :
    CentralSplitCompactQuotientStatement.{u} :=
  centralSplitCompactQuotient_of_splitInputs splitAdelicFundamentalSet splitSiegelOverlap
    (galoisBorelTwisting_of hS1 hS2)

/-- **Springer's compactness theorem** (Springer 1994, Theorem (C), "if" direction): if a
maximal `F`-split torus of a connected reductive group `G` over a number field `F` is
central, then `G(F) \ G(𝔸_F)^1` is compact. -/
theorem centralSplitCompactQuotient : CentralSplitCompactQuotientStatement.{u} :=
  centralSplitCompactQuotient_of_galoisTwist galoisTwistNormOne galoisTwistSubgroup

end Langlands.Global.AdelicSiegelFactors
