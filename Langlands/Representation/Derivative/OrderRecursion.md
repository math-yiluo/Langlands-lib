# Source-rank recursion for actual mirabolic derivatives

This internal helper module adds equality-transport laws and a source-rank
recursion for the existing determinant-normalized derivative functors. It
preserves the supplied topology and independent field and carrier universes.

The source convention is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), registered source
`bernstein-zelevinsky-1977-induced-i`, §3.5 and footnote (2), printed p.452
(one-based PDF p.13), SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The footnote orders the successive minus functors from largest rank to
smallest rank. The formulas below are internal consequences of the existing
Lean definitions, without a new claim about source normalization.

For `h : a = b`, mirabolic rank transport composes transitively and cancels
with its reverse. Transport commutes with `psiMinus`, `phiMinus`, their
iteration, the target-indexed derivative, and the source-rank/order wrapper.
Each proof eliminates the rank equality and uses the identity-functor laws.
These are equalities of complete functors, so they include every morphism.

For `1 ≤ i ≤ N+1`, `mirabolicDerivativeOfOrder_succ` proves
that the order-`i+1` derivative on `mirabolic (N+1)` is `phiMinus T ψ N`
followed by the order-`i` derivative on `mirabolic N`, after the explicit
general-linear rank cast
`N+2-(i+1) = N+1-i`. Its proof writes `i=j+1`, uses the published
`mirabolicDerivative_succ`, and eliminates the equalities
`N = (N+1-i)+(i-1)` and the equal target ranks.
`mirabolicDerivativeOfOrderSuccIso` is the natural isomorphism induced by
this functor equality; its components and inverses are the identity after
equality elimination, and naturality follows for every morphism.

## Proof and source boundary

The proofs use only equality elimination, identity and associativity of functor
composition, `mirabolicDerivative_succ`, the defining equality
`mirabolicDerivativeOfOrder_eq`, and natural-number arithmetic (`omega`). The
wrapper recursion first rewrites both wrappers and then rewrites
`Functor.assoc`; this avoids unfolding the actions while comparing differently
associated compositions. No component of a mixed product is used here.

The equality-induced natural isomorphism has its forward and inverse maps
supplied by `eqToIso`. Eliminating all rank equalities reduces both to identity
intertwiners. The equality is between entire functors, so naturality includes
all morphisms rather than only an object comparison. Both `uF` and `uV` remain
independent. All constructions install the supplied `T.topology`.

This internal recursion preserves exactly the determinant-normalized functors
already defined in `MirabolicMinus`. It does not substitute a Haar modulus or
claim a new comparison with it; no modulus comparison is used in its proof.
The source citation records only the ordering convention. The registered
original was read at PDF pp.11–13, 18–19 and 32, including the rendered ordering
formula on PDF p.13. No source-specific errata file was found in the project
notes or the Library notes; no exhaustive errata search is claimed.

## Complete project import closure

The sole direct import is `Langlands.Representation.Derivative.Homogeneity`.
At Library commit `b22e185743f7c318f709e14e422801f4360105d5`, the complete transitive
project closure (excluding this module, including that direct import) has
54 modules. Every Lean/Markdown pair in this closure was compared byte for byte
with that commit and is unchanged. The list is:

```text

Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
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
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
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

The imported construction path is actual groups and rank maps; local-field
normalization; smooth categories, transfer and twists; algebraic localization;
and the minus-functor iteration and source-rank wrapper. The Whittaker modules
in this list provide algebraic characters, not coinvariant-finiteness results.
`Homogeneity` defines level and homogeneity predicates and proves elementary
wrapper laws; it supplies no mixed-product homogeneity or detection theorem.
The 54-module closure has no project import outside this list. A full source
scan for the excluded conclusion families found no occurrence in its Lean
files; the Markdown mentions of classification are explanatory independence
or downstream-reference passages, not imported mathematics.

## Condition-by-condition independence audit

The two exclusion sets of the BZ77 4.14(a) proof (`LeftMixedProductDerivativeProof`,
which uses this helper through `LeftMixedProductHigher`), including their application to
mathematical conclusions, proofs and transitive dependencies, bind
this helper unchanged. The following records each excluded family against the
complete closure and the actual proof above. For every row, the named
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

This module is a recursion helper, not a proof of the mixed-product
derivative statement. It does not duplicate 4.13(b,c) or assert any of its clauses.
