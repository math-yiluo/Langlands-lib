# Equality transport of left mixed and binary product ranks

This internal helper is derived from equality elimination of the actual
rank-cast functors. It does not assert a mixed-product derivative formula.
The complete proof is: eliminate `h : a = b`, then apply the left and right
identity laws of functor composition. Both products remain unchanged.

`leftMixedProduct_rankCast T k h` identifies transport of the second input
from `mirabolic a` to `mirabolic b`, followed by the left mixed product at
ranks `k,b`, with the product at ranks `k,a` followed by transport along
`k+a = k+b`. `binaryNormalizedProduct_rankCast_right` gives the same identity
for a general-linear second input and the actual binary normalized product.
Both include arbitrary `k,a,b`, in particular every zero rank.

The two `...Iso` definitions apply `eqToIso` to these equalities of complete
functors. Eliminating `h` reduces each component and inverse to identity
intertwiners; the identity laws also give naturality for every pair of input
morphisms. Independent universes `uF` and `uV` and supplied `T.topology` are
preserved. Inputs have carrier universe `uV`; outputs have `max uF uV`.

No new literature assertion is made: provenance is internal equality
transport for the published constructions in `Homogeneity`, `MixedProducts`
and `BinaryProduct`. Their complete Lean/Markdown pairs were read. No Haar
modulus comparison or normalization change is needed.

## Complete project import closure

The direct imports are `Derivative.Homogeneity` and `Mirabolic.MixedProducts`.
Their complete transitive project import closure, including these two and
excluding this entry module, has 73 modules at Library commit
`b22e185743f7c318f709e14e422801f4360105d5`. Every pair was compared byte for
byte with that commit and is unchanged. The full inventory is:

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
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
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

This closure adds only the concrete mixed-product, block induction and tensor
construction layers to the elementary minus-functor/wrapper closure. The actual
proof dependencies of this module are just equality elimination and Mathlib's
`Functor.id_comp` and `Functor.comp_id`. The shared lower products supply their
objects, maps and functor laws; their definitions and proofs use only matrix
blocks, smoothness, real-power characters, tensor maps and compact induction.
No derivative compatibility is part of their proofs. `Tensor.Finite` enters
through `Induction.BlockFactors`, and the generic Whittaker modules supply
algebraic characters. They supply no consumer or finiteness conclusions. A full
scan of all Lean sources in this closure found no occurrence of the excluded
conclusion families. Downstream names in prose are not proof inputs.

## Condition-by-condition independence audit

The two exclusion sets of the BZ77 4.14(a) proof (`LeftMixedProductDerivativeProof`,
which uses this helper through `LeftMixedProductHigher`), including their application to
mathematical conclusions, proofs and transitive dependencies, bind
this helper unchanged. The following records each excluded family against the
complete closure and the actual equality-elimination proof above. For every row, the named
conclusions, their proofs and downstream mathematical consequences
are absent from the import and proof dependencies.

| Condition | Audit result |
| --- | --- |
| Ordered multisegment socle existence and socle exhaustion | No socle construction, existence or exhaustion input. |
| Analytic segment classification | No segment or analytic classification module. |
| Unlinked segment-socle product irreducibility and final criterion | No irreducibility or product criterion. |
| `AdjacentUnlinkedSegmentSocleSwap` | No adjacent commutation. |
| `TwoSegmentSocleCommutation` | No segment commutation. |
| Special-head product criterion | No head or product irreducibility input. |
| Special-head exhaustion | No multisegment or exhaustion result. |
| Ordered special/strong-head existence | No head existence input. |
| Quotient coverage | Only the actual localization construction, no quotient coverage theorem. |
| Tempered uniqueness | No tempered result. |
| `SquareIntegrableLanglandsClassification` | No square-integrable classification. |
| Square-integrable exhaustion and regular exhaustion | No exhaustion result. |
| `GenericSegmentProductUniqueness` | No generic-product or uniqueness input. |
| Ordered special-segment conversion | No conversion input. |
| Forward special-segment essential square-integrability | No square-integrability theorem. |
| Combined Ze80 §5.4 reduction and strong-indecomposability consumers | No indecomposability or reduction theorem. |
| Nonadjacent two-supercuspidal irreducibility and full product structure, including adjacent composition/Jacquet clauses | No supercuspidal or two-factor structure input. |
| Individual special-head/reverse-socle and segment-socle/reverse-head existence | No head or socle existence. |
| Full segment Jacquet formula, head formula, socle formula and special exponent formula | Algebraic localization is present, but no segment Jacquet formula or exponent result. |
| Ze80 §3.5 and §9.6 segment derivative formulas, and the segment-socle part of the derivative statements of `Classification.SegmentSocleDerivativesStatement` | No segment derivative theorem; only defining recursion of general BZ77 functors. |
| Ze80 4.2/9.7 product criteria, 9.3 analytic/square-integrability, classification and exhaustion | None imported or used; no circular use of Ze80 §2/Proposition 1.11. |
| Linked segment reverse-product structure and pair reducibility | No linked-pair result. |
| Juxtaposed reverse-product structure / quotient hom | No such product or quotient-hom input. |
| `LinkedSegmentSocleGluing` | No gluing input. |
| Segment results (b), (d), (e), (f) of `Classification.SegmentSocleDerivativesStatement` | No segment statement or proof module. |
| `SupercuspidalCoinvariantFinitenessStatement` and all-character single-block conclusion | Neither occurs in the closure. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, and mirabolic finite length | No finiteness or finite-length input. |
| Ze80 6.2 consumer (`SegmentSocleProductHomogeneity`), left-product homogeneity (`LeftMixedProductHomogeneity`), GL Leibniz | No consumer conclusion or theorem; the similarly named `Homogeneity` import is only the elementary wrapper module described above. |
| Mirabolic minus exactness | No exactness theorem is needed. |
| Unproved propositions, citations or conditional assemblies as proof evidence | None used as a proved input. Every non-arithmetic proof step is an equality law in the Library or Mathlib, or proved in this module. |

This module asserts only transport laws, and supplies no proof of any mixed-product minus or derivative compatibility clause.
