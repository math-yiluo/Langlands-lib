# Complete Leibniz index partition

Author: Worker 593.

This internal finite-index construction partitions the unchanged Leibniz
family for first rank `m+1` by whether its first derivative order is positive.
The positive block is exactly the unchanged
`RightMixedDerivativeIndex b m d`. The remaining block is a lifted proof of
`d ≤ b`, corresponding to the single pair `(0,d)` when feasible and to an
empty block otherwise.

`leibnizIndexSplitEquiv` preserves the underlying order pair in both blocks.
It does not identify indices whose representations are zero or isomorphic.
Its inverse tests whether the first order is zero; the original sum and
rank bounds establish the appropriate block. The inverse laws use subtype
extensionality and natural-number arithmetic.

`leibnizOptionalIndexEquiv` enumerates the last block by `Fin 1` or `Fin 0`.
`leibnizIndices_card_split` gives the exact sum of the two lengths.
`leibnizSpliceIndexEquiv` accepts any complete enumeration of the positive
block and extends it to the full feasible family by the ordinary finite-sum
equivalence. These are combinatorial helpers for the eventual filtration
splice, rather than a proof of a mixed-product or Leibniz filtration.

The two application lemmas identify the extended enumeration on `Fin.castAdd`
and `Fin.natAdd`, the standard left and right splice positions. They follow
by simplifying the finite-sum equivalence. All constructions hold for every
natural `m,b,d`, including order zero, a zero second rank, top order, and an
empty feasible family above total rank. The first source rank is explicitly
`m+1`; no claim about first source rank zero is needed for this partition.

## Import and mathematical dependency audit

The direct project imports are the unchanged
`GeneralLinearDerivativeLeibnizFiltrationStatement` and
`RightMixedProductDerivativeFiltrationStatement`. The only direct Mathlib
import is `Mathlib.Data.Fintype.Sum`. At Library base
`b22e185743f7c318f709e14e422801f4360105d5`, the complete recursive project
import closure contains 77 modules including this entry:

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.LeibnizIndices
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```

The mathematical inputs are precisely the published membership characterizations
and elementary bound/sum consequences for the two finite index sets, subtype
extensionality, natural-number arithmetic, proof irrelevance, and Mathlib's
finite cardinality and sum-equivalence laws. Neither imported filtration
assertion nor either conditional filtration extractor is used. This pair
constructs no representation map and assumes no exactness, mixed-product
formula, tensor-commutation theorem or Leibniz assertion. Its internal
provenance is the direct partition of the already published index definitions;
no additional literature theorem is required.

| Inherited condition or exclusion | Check for this pair |
| --- | --- |
| Actual functors, natural filtration and unchanged target | This is solely an index helper for those unchanged functors. It preserves every feasible pair; it makes no claim to construct the filtration itself. Both imported Lean/Markdown pairs and their transitive dependencies are unchanged from the pinned base. |
| Arbitrary carriers and independent universes; all boundary ranks and orders | The constructions quantify only over natural numbers and have no carrier or universe hypothesis. The first rank is `m+1`, with all `b,d` allowed, so the zero second rank, order zero and top order are included. No representation or chosen vector is collapsed or discarded. |
| Accepted general upstream inputs; no conditional consumer replacement | Only proved arithmetic lemmas about the unchanged index definitions are used. The imported proposition definitions and their conditional extractors supply no proof hypothesis. |
| Segment derivatives, existence, Jacquet or exponent formulas; analytic classification and Ze80 segment formulas or criteria | No segment module is in the closure. No such result occurs in the elementary finite-set proof terms. |
| Unlinked, linked or juxtaposed segment structures; reducibility, reverse quotients, adjacent swaps, two-segment commutation, gluing and ordered socle existence or exhaustion | No corresponding consumer module or conclusion supplies an input. |
| Special-head criterion, generic segment product uniqueness, multisegment exhaustion, strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | No head, socle, multisegment, classification or exhaustion result is imported or used. |
| Square-integrable classification, square-integrable or regular exhaustion and forward special essential square-integrability | No square-integrability or classification module is imported; the proofs use only the finite-set laws described above. |
| Two-supercuspidal nonadjacent irreducibility and full-product structure/assembly; no consumer proving its upstream input | No supercuspidal or downstream product-consumer conclusion is used. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker finiteness, all-character single-block finiteness and dependent mirabolic finite length | The two inherited Whittaker imports construct characters, functionals and models. No prohibited finiteness assertion or mirabolic finite-length input supplies a proof step. |

A recursive import scan verified the exact closure above and that all 76
imported project Lean/Markdown pairs match the pinned Library. A bounded scan
for the inherited excluded task identifiers and conclusion names found no
matches in the Lean closure. Reading the new terms and their finite-set
inputs also establishes mathematical independence from those excluded
conclusions. This focused helper leaves the all-rank Leibniz proof open.
