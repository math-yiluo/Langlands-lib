import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismAssembly
import Langlands.GroupScheme.Reductive.AffineSplitWeylNormalization
import Langlands.GroupScheme.Reductive.AffineSplitRootSpaceTransport
import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormal
import Langlands.GroupScheme.Reductive.LocalSplitRankOneBruhat
import Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction
import Langlands.GroupScheme.Reductive.LocalSplitNegSimple
import Langlands.GroupScheme.Reductive.LocalSplitWeylConjugationReduction
import Langlands.GroupScheme.Reductive.LocalSplitRootPairUniqueness
import Langlands.GroupScheme.Reductive.LocalSplitRootPairRescaling

/-! # The Isomorphism Theorem for split reductive groups over an affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The unchanged affine split Isomorphism Theorem, in every universe. -/
theorem affineSplitIsomorphismTheorem :
    AffineSplitIsomorphismTheoremStatement.{u} := by
  have hC : LocalSplitWeylConjugationStatement.{u} :=
    localSplitWeylConjugation_of_partner localSplitRootPartnerUniqueness localSplitRootPairRescaling
  apply affineSplitIsomorphismTheorem_of_weylRelations
  · intro R _ G _ hG I _ _ i hi hmax J P hP hfree b
    exact AffineSplitWeylNormalization.exists_simpleRootFamily_of_free
      hG i hi hmax hP hfree b
  · exact localSplitWeylCommutator_of_weylConjugation
      localSplitRankOneNormal hC
  · exact localSplitWeylNegSimple_of_rankOne
      localSplitRankOneNormal localSplitRankOneBruhat hC
  · intro R _ I I' _ _ _ _ H _ J J' P Q i' e hfree α
    exact LocalSplitCell.nonempty_exponentWeightSpace_precompTorus e i' hfree α

end Langlands.GroupScheme
