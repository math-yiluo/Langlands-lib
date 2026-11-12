import Langlands.GroupScheme.Rational.SemigroupComparisonFourPrerequisites
import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusProof
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof
import Langlands.GroupScheme.Adjoint.ExistenceStatement
import Langlands.GroupScheme.Adjoint.Assembly
import Langlands.GroupScheme.Adjoint.CenterQuotientReductiveProof
import Langlands.GroupScheme.Adjoint.CenterQuotientDescent
import Langlands.GroupScheme.Adjoint.SecondCenterReductive
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.NormalQuotientExistenceProof
import Langlands.GroupScheme.Adjoint.NormalEquivariantRetractionReduction
import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementConstruction
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Proof: semigroup functoriality, smooth quotients and CGP 3.3.10 intersections -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

/-- **Semigroup comparison.** Equivariant functoriality of the actual semigroup
subgroup functors, the actual smooth surjection between arbitrary representatives
under a smooth equivariant surjection, and CGP Proposition 3.3.10 intersection
equality in each of its three cases, at every universe. -/
theorem semigroupComparison : SemigroupComparisonStatement.{u} := by
  -- The full-centre adjoint quotient: fppf quotient by the centre representative.
  have hExist : AdjointQuotientExistenceStatement.{u} := by
    intro k _ G hG
    have : Smooth G.X.hom := hG.smooth
    obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
    obtain ⟨Q, q, hQa, hQf, hq⟩ :=
      normalSubgroupQuotientExistence k G Z z hG.isAffineHom inferInstance hz.1 hz.isNormal
    rw [hz.2] at hq
    have hQ : IsConnectedReductive Q := centerQuotientReductive k G Q q hG hQa hQf hq
    have hc : center Q = ⊥ :=
      CenterQuotientCenter.center_eq_bot_of_secondCenterTrivial q hq
        (SecondCenter.secondCenterTrivial_of_centralDerivedProduct
          reductiveCentralDerivedProduct k G hG)
    obtain ⟨hflat, hsurj, hlfp, hker⟩ := hq
    exact ⟨Q, q, isAdjointQuotient_of_fppf_kernel_range q hG hQ hc hflat hsurj hlfp hker⟩
  -- The equivariant retraction onto a normal adjoint subgroup, through commuting
  -- normal complements and generation by normal almost-simple subgroups.
  have hRetraction : NormalAdjointEquivariantRetractionStatement.{u} :=
    normalAdjointEquivariantRetraction_of_semisimpleNormalComplement
      (semisimpleNormalComplement_of_almostSimpleGeneration
        (semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter
          (semisimpleRootGenerationReduction rootRankOneFactorization
            (algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
              solvableTorusQuotient))
          absoluteRootVectorLine maximalTorusConjugacy))
  exact semigroupComparison_of_fourPrerequisites
    ⟨hExist, fixedCenterContainingTorus, hRetraction, Torus.solvableFixedContainmentConnected⟩

end Langlands.GroupScheme.RelativeRoot
