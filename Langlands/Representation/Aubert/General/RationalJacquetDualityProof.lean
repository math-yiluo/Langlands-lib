import Langlands.Representation.Aubert.General.RationalJacquetDualityStatement
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityProof
import Langlands.Representation.Aubert.General.IwahoriNaturalJacquetDuality

/-! # Proof of natural opposite-Jacquet duality on the actual rational-point group

The published generic coherent-naturality theorem
`exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus` is
specialized to the standard radical `unipotent i ν I`, the literal standard Levi `levi i ν I`
and the inverse-cocharacter opposite radical `oppositeUnipotent i ζ`. Its inputs are the
published normalizer inclusions and closedness of both radicals, the Levi-central contracting
point and two-sided basis from `rationalOppositeIwahoriBasisStatement`, and full Haar
reciprocity from `rationalOppositeHaarReciprocity`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Normalized Jacquet restriction of the smooth dual is naturally the smooth dual of
opposite Jacquet restriction on admissible objects, for every standard cocharacter. -/
theorem rationalNaturalJacquetDuality : RationalNaturalJacquetDualityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard I hU ζ hζ
  obtain ⟨g, hc, hb⟩ :=
    rationalOppositeIwahoriBasisStatement k G hG T i hi ν hν hStandard I hU ζ hζ
  exact exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus
    (unipotent i ν I) (levi i ν I) (oppositeUnipotent i ζ) hU
    (isClosed_oppositeUnipotent_localField i ζ)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I).levi_le_normalizer
    (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ).levi_le_normalizer
    g hc hb (rationalOppositeHaarReciprocity k G hG T i hi ν hν hStandard I hU ζ hζ)

end Langlands.Aubert.General.RationalPointFamily
