import Langlands.GroupScheme.Reductive.MultiplicativeTypeNormalCentralStatement
import Langlands.GroupScheme.Reductive.MultiplicativeTypePreimageCentrality
import Langlands.GroupScheme.Reductive.MultiplicativeTypePreimageReduction
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeCoefficientExtension
import Langlands.GroupScheme.Torus.MultiplicativeTypeFibralCriterionProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalDeformationProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof

/-! # Normal subgroups of multiplicative type are central: proof

Conrad, *Reductive group schemes* (2014), Lemma 3.3.1, from the extension property of groups of
multiplicative type (Conrad, Corollary B.4.2(2)).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- **Conrad, Lemma 3.3.1**, assuming the extension property of groups of multiplicative type
(`MultiplicativeTypeFpqcExtensionStatement`, Conrad, Corollary B.4.2). -/
theorem multiplicativeTypeNormalCentral_of_extension
    (hExt : MultiplicativeTypeFpqcExtensionStatement.{u}) :
    MultiplicativeTypeNormalCentralStatement.{u} := by
  intro S G _ _ hG H h hh hH hn
  refine ⟨MultiplicativeTypeNormalCentral.isCentral_of_isNormal_of_isClosedSubgroup G hG h hh hH
    hn, ?_⟩
  intro Q q hq H' h' hh' hH' hc' P p hp
  refine ⟨?_, MultiplicativeTypePreimageCentral.isCentral_preimage G hG h hh hH hn q hq h' hH'
    hc' p hp⟩
  have := hH.locallyOfFinitePresentation
  have := hH'.locallyOfFinitePresentation
  have := hH'.isAffineHom
  have : IsClosedImmersion h'.hom.hom.left := hh'
  have : Mono h'.hom.hom := Over.mono_of_mono_left _
  exact SubgroupPreimage.isMultiplicativeType_represented_of_isCentral_inclusion q h' h hExt hh
    hh' hq hH hH' (MultiplicativeTypePreimageCentral.isCentral_preimage G hG h hh hH hn q hq h'
      hH' hc' _ (SubgroupPreimage.isRepresentedBy_inclusion q h')) hp

/-- **Conrad, Lemma 3.3.1.** Let `G` be a smooth affine group over a scheme `S` with connected
residue fibres. A normal closed subgroup `H` of multiplicative type is central. Take an fppf
quotient `q : G → Q` by `H` and a central closed subgroup `H'` of `Q` of multiplicative type.
Then every `p : P → G` representing the preimage of `H'` under `q` is central, and `P` is of
multiplicative type. -/
theorem multiplicativeTypeNormalCentral : MultiplicativeTypeNormalCentralStatement.{u} :=
  multiplicativeTypeNormalCentral_of_extension
    (ExtensionReduction.fpqcExtension_of_threeStatements multiplicativeTypeFibralCriterion
      multiplicativeTypeCompleteLocalDeformation multiplicativeTypeFieldExtension)

end Langlands.GroupScheme
