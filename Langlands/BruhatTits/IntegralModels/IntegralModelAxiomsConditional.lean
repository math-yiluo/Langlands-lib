import Langlands.BruhatTits.IntegralModels.ModelAxiomsUnramified
import Langlands.BruhatTits.IntegralModels.MorphismAxiomsUnramified
import Langlands.Geometry.Building.UnramifiedApartmentDescentStatement
import Langlands.Geometry.Building.IntegralModelAxiomsStatement
import Langlands.Geometry.Building.UnramifiedOneFixerClosureProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusClause
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumProof
import Langlands.Geometry.Building.UnramifiedZeroFixerAffineRootProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderProof
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalProof
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelProof

/-! # KP Axioms 4.1.20 and 4.1.22 on supplied data from the unramified statements -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building IntegralModel

set_option maxHeartbeats 4000000 in
/-- **KP Axioms 4.1.20 and 4.1.22 from the unramified statements.** Granting the
apartment-compatible unramified descent of the building, the existence of the parahoric
models over the maximal unramified integers (KP 8.3.2/8.3.13), smooth descent of models
(KP Fact 2.10.16), the descent of `G(K)^0` (KP Proposition 9.3.24), the extension of
homomorphisms of smooth models (KP Corollary 2.10.10), the closure invariance of
`G(K)^1`-fixers, the affine-root description of `G(K)^0`-fixers, the torus clause over
`𝒪[F]`, the kernel statement of KP Proposition 8.4.15 over the maximal unramified integers
and the five facet statements of KP Axiom 4.1.22, the target statement
`IntegralModelAxiomsStatement` holds. -/
theorem integralModelAxiomsStatement_of_unramified
    (hapt : UnramifiedApartmentDescentStatement.{u})
    (hpar : UnramifiedParahoricModelStatement.{u})
    (hdesc : UnramifiedSmoothModelDescentStatement.{u})
    (hzero : UnramifiedZeroDescentStatement.{u})
    (hext : UnramifiedSmoothHomExtensionStatement.{u})
    (hclos : UnramifiedOneFixerClosureStatement.{u})
    (hroot : UnramifiedZeroFixerAffineRootStatement.{u})
    (htor : UnramifiedTorusClauseStatement.{u})
    (hker : UnramifiedModelKernelStatement.{u})
    (hS1 : UnramifiedFacetParabolicImageStatement.{u})
    (hS2 : UnramifiedFacetParabolicOrderStatement.{u})
    (hS3 : UnramifiedFacetCommonTorusStatement.{u})
    (hS4 : UnramifiedFacetRootDatumStatement.{u})
    (hS5 : UnramifiedFacetPositiveRadicalStatement.{u}) :
    IntegralModelAxiomsStatement.{u} := by
  intro F _ _ _ _ G _ P R T h1 h2 h3 h4 h5 h6 h7
  obtain ⟨C, A, e, a, he_inj, he_smul, he_apt, hA_fix, hA_surj, hspecial, hfacet, hkernel⟩ :=
    hapt F G P.isConnectedReductive P.toValuationBuildingData
  obtain ⟨M, hM, hpts⟩ := BuildingModelFamily.exists_satisfiesModelAxioms_of_unramified P R T
    h1 h2 h3 h4 h5 h6 h7 hpar hdesc hzero hext hclos hroot htor C A e a he_inj he_smul he_apt
    hA_fix hfacet hkernel
  obtain ⟨Q, ρ, hQ⟩ := BuildingModelFamily.exists_satisfiesMorphismAxioms_of_unramified P R T
    h1 h2 h3 h4 h5 h6 h7 hker hS1 hS2 hS3 hS4 hS5 M C A e a he_inj he_smul he_apt hA_fix
    hA_surj hspecial hfacet hkernel (unramifiedZeroDatumOfParahoric P) hpts hM.torus_clause
  exact ⟨M, Q, ρ, hM, hQ⟩

/-- **Reduction to apartment descent and zero-subgroup descent.** The parahoric
models `unramifiedParahoricModel`, the smooth descent `unramifiedSmoothModelDescent`, the
homomorphism extension `unramifiedSmoothHomExtension`, the closure invariance
`unramifiedOneFixerClosure`, the affine-root description `unramifiedZeroFixerAffineRoot`,
the torus clause `unramifiedTorusClause`, the kernel statement `unramifiedModelKernel`, the
facet parabolic-order statement `unramifiedFacetParabolicOrder`, the facet common-torus
statement `unramifiedFacetCommonTorus`, the facet root-datum statement
`unramifiedFacetRootDatum` and the facet positive-radical statement
`unramifiedFacetPositiveRadical` are Library proofs. The facet parabolic-image statement is
obtained from the Library reduction
`unramifiedFacetParabolicImage_of_generation_positive_modelKernel`, applied to the Library
proofs `unramifiedUpstairsRadicalRootGeneration`, `unramifiedFacetPositiveRadical` and
`unramifiedModelKernel`. The theorem takes apartment descent and zero-subgroup descent
as hypotheses. -/
theorem integralModelAxiomsStatement_of_unramified_remaining
    (hapt : UnramifiedApartmentDescentStatement.{u})
    (hzero : UnramifiedZeroDescentStatement.{u}) :
    IntegralModelAxiomsStatement.{u} :=
  integralModelAxiomsStatement_of_unramified hapt unramifiedParahoricModel
    unramifiedSmoothModelDescent hzero
    unramifiedSmoothHomExtension unramifiedOneFixerClosure unramifiedZeroFixerAffineRoot
    unramifiedTorusClause unramifiedModelKernel
    (unramifiedFacetParabolicImage_of_generation_positive_modelKernel
      unramifiedUpstairsRadicalRootGeneration unramifiedFacetPositiveRadical
      unramifiedModelKernel)
    unramifiedFacetParabolicOrder unramifiedFacetCommonTorus
    unramifiedFacetRootDatum unramifiedFacetPositiveRadical

end Langlands.BruhatTits.IntegralModels
