import Langlands.GroupScheme.Torus.SelfCentralizingWeylAffinenessStatement
import Langlands.GroupScheme.Torus.SeparatedWeylQuotient
import Langlands.GroupScheme.Torus.SelfCentralizingWeylAffinenessCriterion
import Langlands.GroupScheme.Torus.SeparatedNormalizerProof
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientProof

/-! # Proof of the self-centralizing Weyl affineness statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open SelfCentralizingWeylAffineness in
/-- **Weyl quotient and affineness criterion** for a self-centralizing maximal torus
(SGA 3, Exposé XV, Proposition 7.1(iv), and Exposé XVI, Theorem 4.1(c)–(d)).

The normalizer and the Weyl quotient come from
`exists_selfCentralizingTorusWeylQuotient` applied to `separatedTorusNormalizer`;
the affineness criterion is `isAffineHom_iff` applied to
`selfCentralizingTorusConjugacyQuotientAffine`. -/
theorem selfCentralizingTorusWeylAffineness :
    SelfCentralizingTorusWeylAffinenessStatement.{u} := by
  intro S G hsmooth hsep hqc hfib T t hT ht hmax hcent
  have : Smooth G.X.hom := hsmooth
  have : IsSeparated G.X.hom := hsep
  have : QuasiCompact G.X.hom := hqc
  obtain ⟨N, n, W, q, hnc, hn, hN, hWsep, hWqc, hWet, hflat, hsurj, hlfp, hker⟩ :=
    exists_selfCentralizingTorusWeylQuotient separatedTorusNormalizer G t hT ht hcent
  exact ⟨N, n, W, q, hnc, hn, hN, hWsep, hWqc, hWet, hflat, hsurj, hlfp, hker,
    isAffineHom_iff selfCentralizingTorusConjugacyQuotientAffine G hsmooth hsep hqc hfib
      T t hT ht hmax hcent n q hnc hn hflat hsurj hlfp hker⟩

end Langlands.GroupScheme
