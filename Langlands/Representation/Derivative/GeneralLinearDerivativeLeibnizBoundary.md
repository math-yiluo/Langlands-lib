# Order-zero general linear derivative Leibniz filtration

Author: Worker 593.

This pair proves the `d = 0` instance of the unchanged
`GeneralLinearDerivativeLeibnizFiltrationStatement` for every factor rank and
arbitrary smooth carriers. It does not prove its positive-order instances.

The literal `leibnizSource` at order zero equals the actual binary normalized
product followed by `SmoothRep.toRep`. Every feasible index is `(0,0)`.
Both factor derivatives are the published identity functors at order zero,
and the published smooth rank cast is the identity. Thus `leibnizPiece_zero`
identifies the unchanged grade with the same product functor.
`leibnizZeroFiltration` is the actual two-step chain from zero to the whole
source. `leibnizZeroGradedIso` identifies its actual quotient naturally with
the unchanged feasible piece, using `Filtration.OneStep`.
`generalLinearDerivativeLeibnizFiltration_zero` enumerates the complete feasible
singleton by `Finset.equivFin` and proves the exact order-zero gluing conclusion.

The source is Bernstein and Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, printed p.458, Corollary 4.14(c), whose
order parameter includes zero. The implemented order-zero proof is elementary:
it uses only the definition of derivative order zero and the actual quotient
by zero. Rank-zero factors retain their full tensor carriers through the
unchanged binary product; neither factor is replaced by a tensor unit.

The imports are the unchanged target statement and the generic one-step
filtration pair. The mathematical proof uses identity derivative/rank-cast
laws from `Derivative.Iteration`, feasible-singleton lemmas from the target,
and the quotient first-isomorphism theorem from `Filtration.QuotientFirstIso`.
No positive-order derivative input, exactness, mixed-product derivative theorem,
segment formula, classification, irreducibility, exhaustion, or Whittaker
finiteness assertion is a proof hypothesis. The following audit records the complete project import closure.

## Import and mathematical dependency audit

At Library base `b22e185743f7c318f709e14e422801f4360105d5`, a recursive scan of
all import commands gives 73 `Langlands` modules, including this entry module
and the new generic helper. In the exact list below, brace notation expands
each final component into a module name. There are no other project imports.
Mathlib imports supply ordinary categories, representations, module quotients,
tensor products, topological groups, matrices, finite sets, local fields and
proof tactics; they do not import any project module.

- `Langlands.Group.GL.{Basic, BlockModulus, Blocks, Mirabolic, MirabolicOppositeIntersection, MirabolicRadical, Nonarchimedean, NonarchimedeanStatement, NormalizedCharacter, OppositeBlocks, Padic, PadicBlocks, RankMaps, RankReindex, UpperUnipotent}`
- `Langlands.HarmonicAnalysis.{Basic}`
- `Langlands.LocalField.{Canonical, Definitions, Topology}`
- `Langlands.LocalField.Normalization.{Definitions, Proof, Statement}`
- `Langlands.Representation.Category.{Basic, Twist}`
- `Langlands.Representation.Derivative.{GeneralLinearDerivativeLeibnizBoundary, GeneralLinearDerivativeLeibnizFiltrationStatement, Iteration, MirabolicCharacter, MirabolicMinus}`
- `Langlands.Representation.Dual.{Definitions}`
- `Langlands.Representation.Filtration.{Definitions, OneStep, QuotientFirstIso}`
- `Langlands.Representation.Induction.{BinaryProduct, BlockFactors, Definitions, Parabolic}`
- `Langlands.Representation.Jacquet.{Coinvariants, Localization, PositiveCharacter, SmoothTwist}`
- `Langlands.Representation.MatrixCoefficient.{Definitions, LawsProof, LawsStatement}`
- `Langlands.Representation.Smooth.Admissibility.{CofinalProof, CofinalStatement}`
- `Langlands.Representation.Smooth.{Definitions}`
- `Langlands.Representation.Smooth.SmoothPart.{BasicProof, BasicStatement, Definitions}`
- `Langlands.Representation.Smooth.Transfer.{PullbackProof, PullbackStatement, SubquotientProof, SubquotientStatement}`
- `Langlands.Representation.Tensor.{Finite, OneFactor}`
- `Langlands.Representation.Twist.{AdmissibilityProof, AdmissibilityStatement, AlgebraProof, AlgebraStatement, ContinuousCharacterProof, ContinuousCharacterStatement, Definitions, RealPower, SmoothProof, SmoothStatement, SubquotientDefinitions, SubquotientProof, SubquotientStatement}`
- `Langlands.Representation.Whittaker.{Algebraic, GeneralLinear}`
- `Langlands.Topology.{CompactNormCharacter}`
- `Langlands.Topology.Nonarchimedean.{Subgroup}`

The proof dependencies are narrower than these imports. The new quotient
isomorphism uses only the generic first-isomorphism constructor and the proved
zero-kernel and surjectivity of the full inclusion. The boundary comparison
uses only the two identity-functor equations and the existing feasible-index
singleton. `leibnizSource` and `leibnizPiece` retain the actual product without
using any nontrivial property of it. The accepted target's conditional
`.filtration` extractor is not used. These are all proof inputs.

| Inherited requirement or exclusion | Verification for this contribution |
| --- | --- |
| Actual natural filtration; complete enumeration; repeated and zero grades permitted | The endpoints are actual subfunctors, the grade is their actual quotient functor, its identification is a natural isomorphism, and `Finset.equivFin` enumerates the entire singleton. A zero product still has this one grade. |
| Independent field and carrier universes; no extra representation hypothesis | The parameters retain `uF,uV`, the supplied topology and bundled additive character. All ranks and smooth carriers are arbitrary. The only bound is the original order bound `0 ≤ a+b`. |
| Zero ranks and zero order; top order at total rank zero | Both derivatives and the smooth rank cast reduce to identities. The original binary product retains both carriers. No `P_0`, chosen vector, finite dimension, admissibility, genericity or finite length is introduced. |
| General restriction, minus, exactness, tensor and filtration inputs must be proved | Only elementary order-zero construction equations and the published generic quotient theorem are used. No positive-order, exactness, mixed derivative or tensor-commutation premise is assumed. |
| Segment derivative, socle/head existence, all segment Jacquet and exponent formulas, analytic segment classification; Ze80 §§3.5, 9.6, 4.2, 9.7, 9.3 | No corresponding module occurs in the closure and no such declaration is used. The source comparison is BZ77 4.14(c) at order zero, not a segment derivative formula. |
| Unlinked, linked and juxtaposed segment product structures, pair reducibility, reverse quotients, adjacent swaps, two-segment commutation, gluing, ordered socle existence and socle exhaustion | No socle or segment module occurs in the closure; the implemented proof uses only the algebraic inputs listed above. |
| Special-head criterion; generic segment product uniqueness; multisegment exhaustion, strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | No such module or conclusion occurs in the closure or supplies a proof input. |
| Square-integrable Langlands classification, square-integrable and regular exhaustion, forward special essential square-integrability | No classification or square-integrability module occurs in the closure; no such conclusion supplies a proof input. |
| Two-supercuspidal nonadjacent irreducibility and full-product structure/assembly, or any consumer proving its own upstream input | No two-supercuspidal module occurs in the closure and no consumer result is used. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker coinvariant finiteness; all-character single-block finiteness and dependent mirabolic finite-length route | The closure's two Whittaker modules define algebraic characters and the general-linear character, without any finiteness input. No prohibited finiteness conclusion or mirabolic finite-length result is used. |
| Preserve the target and all imported Lean/Markdown pairs | This contribution adds only this pair and `Filtration.OneStep`; the published target and every imported pair are unchanged. |

These checks cover direct and transitive proof dependencies: the complete
project import graph has none of the excluded families, and the new proof
terms use only the explicit elementary inputs above. This is an order-zero
helper contribution and does not discharge the all-rank positive-order target.
