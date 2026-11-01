# Natural identification of positive Leibniz grades

Author: Worker 593. The supporting `RankCastCompat` pair is coauthored by
Workers 593 and 984.

This internal helper identifies the unchanged right mixed derivative grade,
after restricting its first input from `GL_(m+1)` and transporting its output
rank, with the unchanged `leibnizPiece` at the same order pair. It constructs
natural isomorphisms of the full functors, retaining their maps as well as
their objects. It assumes no filtration or derivative exactness assertion.

`generalLinearRepRankCast` is equality transport of the identity functor on
actual representations, with arbitrary carrier universe. The proved square
`generalLinearRankCast_toRep` says that the actual smooth rank cast followed
by forgetting equals forgetting followed by this representation rank cast.
Eliminating the rank equality reduces the square to the two identity-functor
laws. Thus the representation-valued interface below retains the target's
prescribed smooth transport before forgetting.

For `x : RightMixedDerivativeIndex b m d`, write its orders as `(i,j)`.
They satisfy `0 < i`, `i ≤ m+1`, `j ≤ b`, and `i+j=d`.
`leibnizPositiveSmoothPieceIso` first applies the natural identification of
restriction followed by the order-`i` mirabolic derivative with the actual
order-`i` general-linear derivative. Its product with the identity comparison
for the order-`j` second derivative is then whiskered by the actual binary
normalized product, both smooth output rank casts, and forgetting. The two
output casts compose, since their intermediate total ranks are equal; their
composite has the same endpoints as the cast in `leibnizPiece`. Unfolding
the unchanged piece definitions and using proof irrelevance finishes the
functor equality. There is no extra determinant twist or factor exchange.

`leibnizPositivePieceIso` gives the direct interface for the published
`Rep`-valued `rightMixedDerivativePiece`. It precomposes that functor by
`(generalLinearRestriction T m).prod (𝟭 _)` and postcomposes by the rank
transport from `(b+m)+1-d` to `((m+1)+b)-d`. The proved forgetting square
and functor associativity identify this with the source of the preceding
smooth comparison. Composing yields the required natural isomorphism with
`leibnizPiece T ψ (m+1) b d (leibnizPositiveIndex x)`.

The field universe `uF` and input carrier universe `uV` are independent.
The forgetting square holds at every carrier universe; the direct grade
comparison uses it at the actual product output universe `max uF uV`.
The supplied topology and bundled continuous nontrivial character are
retained. The first rank is `m+1`, while `b,d` are arbitrary natural numbers
and feasibility is carried by `x`. In particular, the second factor may
have rank zero with an arbitrary carrier, and either derivative output may
have rank zero. Top orders retain both actual top-derivative carriers.
At order zero there is no positive-first index, so this helper makes no
order-zero filtration claim. It does not address first source rank zero.
No admissibility, irreducibility, finite dimension or length, genericity,
chosen vector, or equality of carrier and field universes is imposed.

## Import and mathematical dependency audit

The direct project imports are `RankCastCompat` and `LeibnizIndices`;
there is no direct Mathlib import. At Library base
`b22e185743f7c318f709e14e422801f4360105d5`, the complete recursive project
import closure contains 79 modules including this entry. The two supporting
pairs are supplied unchanged; the remaining 76 imported Lean/Markdown pairs
are unchanged from that base.

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
Langlands.Representation.Derivative.LeibnizPieceCompat
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.RankCastCompat
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

The mathematical inputs are the proved positive-order defining equation for
the actual general-linear derivative, the restriction/derivative natural
isomorphism from `RankCastCompat`, the proved composition law for equality
rank casts, the unchanged positive-index inclusion and its bound/sum/rank
laws, products and whiskering of natural isomorphisms, functor identity and
associativity laws, equality transport, proof irrelevance, and elementary
natural-number arithmetic. The internal provenance is precisely this
comparison of already defined functors. It needs no additional literature
theorem. Neither imported filtration proposition nor its conditional
extractor supplies a premise or a proof step.

| Inherited condition or exclusion | Check for this pair |
| --- | --- |
| Actual functors, complete natural filtration, unchanged target and smooth output cast | The helper compares the literal mixed grade with its literal Leibniz grade as whole functors. The forgetting square proves that the final representation cast is exactly the prescribed smooth cast before forgetting. The target and all existing imported pairs remain unchanged. No filtration is claimed. |
| Arbitrary carriers, independent universes and all boundaries | The comparison has arbitrary `b,d`, feasible `x`, supplied topology and character, and independent input universes. Zero second rank and zero output ranks retain their arbitrary carriers. The first rank is explicitly positive; at order zero the positive block is empty. |
| Accepted general upstream inputs; no conditional consumer replacement | The only representation-theoretic equation used is the proved defining equation of positive differentiation, packaged in `RankCastCompat`. No exactness, mixed-product filtration, tensor-commutation theorem, or Leibniz assertion is assumed. |
| Segment derivatives, existence, Jacquet or exponent formulas; analytic classification and Ze80 segment formulas or criteria | No segment module is in the closure. No such result supplies an input to the comparison of the defining functors. |
| Unlinked, linked or juxtaposed segment structures; reducibility, reverse quotients, adjacent swaps, two-segment commutation, gluing and ordered socle existence or exhaustion | No corresponding consumer module or conclusion supplies an input. |
| Special-head criterion, generic segment product uniqueness, multisegment exhaustion, strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | No head, socle, multisegment, classification or exhaustion result is imported or used. |
| Square-integrable classification, square-integrable or regular exhaustion and forward special essential square-integrability | No square-integrability or classification module is imported or used. |
| Two-supercuspidal nonadjacent irreducibility and full-product structure/assembly; no consumer proving its upstream input | No supercuspidal or downstream product-consumer conclusion is used. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker finiteness, all-character single-block finiteness and dependent mirabolic finite length | The two inherited Whittaker imports provide character, functional and model constructions. No prohibited finiteness or mirabolic finite-length assertion supplies a proof step. |

A recursive import scan verified this exact closure and the unchanged
supporting pairs. A bounded scan for the inherited excluded task identifiers
and conclusion names found no matches in the Lean closure. Reading the new
terms and their defining-equation inputs also establishes mathematical
independence from those excluded conclusions. The full all-rank Leibniz
filtration remains a separate open proof obligation.
