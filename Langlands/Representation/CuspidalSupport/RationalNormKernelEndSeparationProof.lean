import Langlands.Representation.CuspidalSupport.RationalNormKernelEndSeparationStatement
import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeSeparation
import Langlands.Representation.CuspidalSupport.RationalNormKernelEndDomainProof
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter

/-! Renard VI.4.3, Lemma: simple right modules separate `End (ind_{⁰G}^G ρ)`. The group `G(F)`
is second countable, so `G ⧸ ⁰G` is countable and the irreducible smooth `ρ` has countable
dimension; with the unique-products property of `G ⧸ ⁰G`, the generic result of
`NormalSubgroupHeckeSeparation` applies to the open normal subgroup `⁰G`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.3, Lemma. -/
theorem rationalNormKernelEnd_separation :
    RationalNormKernelEndSeparationStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  have : SecondCountableTopology (GroupScheme.rationalPoints G) :=
    (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  have : SecondCountableTopology (rationalCommonNormKernel G) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  intro ρ hρ I α hα
  have : ρ.representation.IsIrreducible := hρ
  have := rationalNormKernelQuotient_uniqueProds G
  have := NormalHecke.countable_quotient_of_isOpen (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G)
  exact NormalHecke.separation (rationalCommonNormKernel G) ρ (isOpen_rationalCommonNormKernel G)
    (Whittaker.MirabolicRigidity.rank_le_aleph0 ρ.representation ρ.isSmooth hρ) α hα

end Langlands.CuspidalSupport
