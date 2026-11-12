import Langlands.GroupScheme.SimplyConnected.AnisotropicFactorCentralizerStatement
import Langlands.GroupScheme.SimplyConnected.NormalFactorRetraction
import Langlands.GroupScheme.Rational.AnisotropicKernelCentralizer
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementGeneration
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Anisotropic almost-simple factors centralize the maximal split torus: proof -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Anisotropic factors centralize a maximal split torus.** Over every field, every
anisotropic closed normal almost-simple subgroup of a simply connected group lies, on
every test scheme, in the centralizer functor of a maximal split torus. -/
theorem simplyConnectedAnisotropicFactorCentralizer :
    SimplyConnectedAnisotropicFactorCentralizerStatement.{u} := by
  -- The arbitrary-field normal-isogeny complement, from the published proofs of
  -- almost-simple generation over algebraically closed fields.
  have hComplement : SemisimpleNormalIsogenyComplementStatement.{u} :=
    semisimpleNormalIsogenyComplement_of_generation
      (semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter
        (semisimpleRootGenerationReduction rootRankOneFactorization
          (algClosedMaximalTorusCentralizer_fromQuotient
            dynamicCentralizerReductive solvableTorusQuotient))
        absoluteRootVectorLine maximalTorusConjugacy)
  intro k _ G hG S i hi A a hA ha hn hAn
  let : IsAffineHom A.X.hom := hA.isSemisimple.isConnectedReductive.isAffineHom
  -- A retraction `p : G ⟶ A` whose kernel commutes with `A` on every test scheme.
  obtain ⟨p, _, hker⟩ :=
    hG.exists_normalFactorRetraction_of_complement hComplement a ha
      hA.isSemisimple.isConnectedReductive.smooth
      hA.isSemisimple.isConnectedReductive.connectedSpace hn
  -- The composite `i ≫ p` from the split torus to the anisotropic `A` is trivial.
  exact hAn.range_le_torusCentralizer_of_kernel_commutes hi.isSplitSubtorus.1 a i p hker

end Langlands.GroupScheme
