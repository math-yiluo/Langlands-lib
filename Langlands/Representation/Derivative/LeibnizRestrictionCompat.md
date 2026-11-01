# Natural source comparisons for the positive-rank Leibniz argument

Author: Worker 593.

This internal helper constructs natural isomorphisms for the actual
differentiated middle and subobject functors of the mirabolic restriction
sequence. The middle term becomes the unchanged `leibnizSource`; the
subobject term becomes the unchanged `rightMixedDerivativeSource`,
precomposed by restriction on the first input and with the common output
rank. These are comparisons of whole functors, including their maps.

The provenance is internal composition of already defined functors and
proved natural comparisons. The constructions use the defining
positive-order general-linear derivative comparison, equality-based rank
transports, their composition law and the forgetting square. No new
original-literature theorem is asserted. The imported restriction and
filtration proposition definitions supply the actual functors being
compared; neither proposition is used as a premise or as a proof.
This module does not construct a restriction sequence, prove exactness,
or prove a filtration assertion.

## Parameters and exact functors

Let `F : PadicField.{uF} p`, `[Fact p.Prime]`, and let
`T : F.TopologicalData` be supplied. The bundled additive character `ψ`
retains its continuity and nontriviality. The carrier universe `uV` is
independent of `uF`. Write `a=m+1`, `b=n+1`, and `N=m+n+1`.
The common input category is the product of the actual smooth
representations of `GL_a` and `GL_b`, with arbitrary carriers in `uV`.
The order hypothesis is precisely `0 < d ∧ d ≤ a+b`.

Both source functors first apply the appropriate actual term
`restrictedProduct T m n` or `restrictionSubobject T m n`, then
`mirabolicDerivativeOfOrder T ψ N d`, then `SmoothRep.toRep`, and then
`generalLinearRepRankCast` along `N+1-d = a+b-d`. They take values in
representations of `GL_(a+b-d)` with carrier universe `max uF uV`.
The representation cast is the published equality transport of the
identity functor. The proved equation `generalLinearRankCast_toRep`
identifies it with the prescribed smooth rank cast before forgetting.
Thus these interfaces retain the original smooth rank transports.

`leibnizRestrictedProductSourceIso` identifies the differentiated
`restrictedProduct` with the literal
`leibnizSource T ψ (m+1) (n+1) d hd.2`. Its implementation has three steps:

1. Unfolding the restricted product gives the actual binary normalized
   product, the smooth cast `a+b=N+1`, and restriction to the mirabolic
   subgroup. Whiskering `generalLinearRestrictionDerivativeIso` replaces
   restriction followed by the order-`d` mirabolic derivative by the
   actual order-`d` general-linear derivative at rank `N+1`.
2. Whiskering `generalLinearRankCastDerivativeIso` moves the input cast
   across that derivative, leaving the actual derivative at rank `a+b`
   followed by the output cast `a+b-d=N+1-d`.
3. The forgetting square moves the representation output cast before
   forgetting. Functor associativity and `generalLinearRankCast_trans`
   compose the two smooth output casts. Their endpoints agree, so the
   composite is the identity rank transport by proof irrelevance.
   The remaining functor is definitionally the literal Leibniz source.

`leibnizRestrictionSubobjectSourceIso` identifies the differentiated
`restrictionSubobject` with
`(generalLinearRestriction T m).prod (𝟭 _)`, then the literal
`rightMixedDerivativeSource T ψ (n+1) m d`, and then the representation
cast `((n+1)+m)+1-d = a+b-d`.
The actual subobject already restricts the first input and uses the
published right mixed product, including its case (III) epsilon.
Whiskering `mirabolicRankCastDerivativeIso` moves the cast
`(n+1)+m=N` across the actual mirabolic derivative. The forgetting
square and the composition law combine the output casts. Unfolding the
unchanged right mixed source then gives the stated functor equality.
There is no factor exchange or extra determinant twist.

All arithmetic witnesses are proved by natural-number arithmetic.
No rank-zero input case or order-zero case is claimed here: the displayed
input ranks and order are positive. The top order `d=a+b` is included,
with the actual output at `GL_0` and its original carrier. The right mixed
source has positive total mirabolic rank because `b=n+1`; the first
restricted input may be `P_1` when `m=0`. No `P_0` is introduced.
The constructions impose no admissibility, irreducibility, finite
dimension or length, genericity, chosen vector, canonical topology or
equality of field and carrier universes.

## Import and mathematical dependency audit

The direct project imports are `Derivative.LeibnizPieceCompat` and
`Derivative.MirabolicProductRestrictionStatement`, under
`Langlands.Representation`. There is no direct Mathlib import.
At Library base `8415f6175c53876deb57d52d6700854f946e8529`,
the recursive project closure contains 81 modules including this entry.
All 80 imported Lean/Markdown pairs byte-match that published base.
No unpublished supporting pair is needed. The complete inventory is:

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
Langlands.Representation.Derivative.LeibnizRestrictionCompat
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
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

The actual mathematical inputs are the defining positive-order
general-linear derivative equation and its published
`generalLinearRestrictionDerivativeIso`; the published general-linear
and mirabolic rank-cast/derivative comparisons; the rank-cast composition
law and forgetting square; products, composition, equality transport
and whiskering of functors and natural isomorphisms; proof irrelevance;
and elementary natural-number equalities. The imported statement modules
contribute their actual source functors. No conditional extractor or
theorem-valued proposition supplies a proof step.

| Inherited condition or exclusion | Check for this pair |
| --- | --- |
| Actual functors, natural filtration target, complete feasible indices, smooth output cast and no residual twist | The new terms compare exactly the actual restricted-product and subobject functors with the unchanged source functors. Both comparisons are natural. The forgetting square identifies the output cast with the prescribed smooth cast. No filtration or enumeration is asserted or modified; all existing pairs remain unchanged. |
| Independent universes, arbitrary carriers, supplied topology and character, zero and top boundaries | The field and input universes are independent, and all carriers remain arbitrary. Input ranks and order are explicitly positive. The top order and its actual `GL_0` carrier are included. Order zero and rank-zero inputs remain separate obligations. |
| Only proved and published general inputs; no consumer replacement for missing restriction, exactness, tensor or filtration proofs | The construction uses the proved defining comparisons and equality transport. It does not use any restriction, mixed-product, exactness, tensor-commutation or Leibniz proposition as a proof. The imported statement definitions only name the compared functors. |
| Segment derivative formulas, segment existence, Jacquet and exponent formulas, analytic classification and Ze80 segment formulas or criteria | No segment module occurs in the closure. None of these mathematical conclusions supplies a proof step. |
| Unlinked, linked or juxtaposed segment structures, reducibility, reverse quotients, adjacent swaps, two-segment commutation, gluing, ordered socle existence and socle exhaustion | No corresponding consumer module is imported, and no such conclusion is used. |
| Special-head criterion, generic segment product uniqueness, multisegment exhaustion, strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | No head, socle, multisegment, classification or exhaustion conclusion is used or imported. |
| Square-integrable classification, square-integrable or regular exhaustion, and forward special essential square-integrability | No square-integrability or classification module is in the closure, and none of these conclusions is used. |
| Two-supercuspidal nonadjacent irreducibility, full-product structure and assembly; no downstream consumer establishing its upstream input | No supercuspidal or downstream product-consumer conclusion is used. These two comparisons follow from the actual defining functors. |
| Irreducible, Levi-cuspidal, supercuspidal and all-character single-block Whittaker finiteness, including dependent mirabolic finite length | The inherited algebraic Whittaker modules provide character, functional and model constructions. No prohibited finiteness or mirabolic finite-length assertion supplies a proof step. |

A recursive source scan checked the complete project closure, the
nonempty Markdown pairs and byte equality of every dependency at the
displayed base. A bounded scan for the inherited excluded declaration
names and task identifiers found no Lean-source matches. The implemented
terms described above also establish the mathematical dependency audit;
the text scan alone is not its justification. The all-rank Leibniz
filtration remains an open separate proof obligation.
