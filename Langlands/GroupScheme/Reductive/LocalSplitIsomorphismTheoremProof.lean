import Langlands.GroupScheme.Reductive.LocalSplitNegSimple
import Langlands.GroupScheme.Reductive.LocalSplitWeylConjugationReduction
import Langlands.GroupScheme.Reductive.LocalSplitRootPairUniqueness
import Langlands.GroupScheme.Reductive.LocalSplitRootPairRescaling
import Langlands.GroupScheme.Reductive.LocalSplitSimpleRootGroupLocal
import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormal
import Langlands.GroupScheme.Reductive.LocalSplitRankOneBruhat

/-! # Proof of the Isomorphism Theorem for split reductive groups over a local ring -/

universe u

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Universality of Weyl conjugation in Weyl families over a local ring**, from partner
uniqueness and inverse rescaling of Weyl-normalized root pairs. -/
theorem localSplitWeylConjugation : LocalSplitWeylConjugationStatement.{u} :=
  localSplitWeylConjugation_of_partner
    (by
      intro R _ _ G _ hG I _ _ i hi hmax J P hP a xp xm xm' hp hm hm' hn hn'
      exact localSplitRootPartnerUniqueness R G hG I i hi hmax J P hP a xp xm xm' hp hm hm' hn
        hn')
    (by
      intro R _ _ G _ hG I _ _ i hi hmax J P hP a xp xm hp hm hn κ
      exact localSplitRootPairRescaling R G hG I i hi hmax J P hP a xp xm hp hm hn κ)

/-- **The Isomorphism Theorem for split reductive groups over a local ring.** -/
theorem localSplitIsomorphismTheorem : LocalSplitIsomorphismTheoremStatement.{u} :=
  localSplitIsomorphismTheorem_of_weylRelations localSplitSimpleRootGroupLocal
    (localSplitWeylCommutator_of_weylConjugation localSplitRankOneNormal
      localSplitWeylConjugation)
    (localSplitWeylNegSimple_of_rankOne localSplitRankOneNormal localSplitRankOneBruhat
      localSplitWeylConjugation)

end Langlands.GroupScheme
