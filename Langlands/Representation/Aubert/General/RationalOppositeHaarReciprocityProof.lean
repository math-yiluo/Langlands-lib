import Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityStatement
import Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Proof of reciprocal actual Haar characters on opposite standard rational radicals

For a standard cocharacter `ζ` of the standard subset `I`, the standard radical, the literal
standard Levi and the opposite radical are the identity-test dynamic subgroups `N(χ⁻¹)`,
`M(χ)` and `N(χ)` of `χ = (groupHom ζ ≫ i)⁻¹`. The published arbitrary-cocharacter reciprocity
`dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus` then applies, with its two
structural premises discharged by the published unconditional theorems
`relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization` and
`centralSplitTorusCharacter`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- On the literal common standard Levi, the actual Haar scaling characters of the standard
radical and of the inverse-cocharacter opposite radical multiply to one. -/
theorem rationalOppositeHaarReciprocity : RationalOppositeHaarReciprocityStatement.{u} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard I hU ζ hζ m
  have : T2Space k := Langlands.BruhatTits.localField_t2Space k
  obtain ⟨-, hM, hUeq⟩ :=
    (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).2 ζ hζ
  exact dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
    (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
    centralSplitTorusCharacter hG
    (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i))
    (unipotent i ν I) (levi i ν I) (oppositeUnipotent i ζ)
    (by rw [Dynamic.inverseCocharacter_inverseCocharacter, ← hUeq])
    (by rw [Dynamic.centralizer_inverseCocharacter, ← hM])
    rfl hU (isClosed_oppositeUnipotent_localField i ζ) _ _ m

end Langlands.Aubert.General.RationalPointFamily
