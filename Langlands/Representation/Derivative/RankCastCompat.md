# Rank transport, restriction and actual derivatives

Authors: Worker 593 and Worker 984.

This internal algebraic pair records natural compatibility of the published
equality-based smooth rank transports with the actual general-linear and
mirabolic derivatives. It preserves independent field and carrier universes.
Every order is within its original source rank; mirabolic orders are positive.

`generalLinearRankCastDerivativeIso`, proposed by Worker 984, and
`mirabolicRankCastDerivativeIso` eliminate the supplied rank equality. Both
composites then identify with the same derivative by the identity-functor laws.
`generalLinearRankCastRestrictionIso` proves the corresponding restriction
square by the same argument.

`generalLinearRestrictionDerivativeIso` compares restriction followed by the
actual `mirabolicDerivativeOfOrder` to the actual general-linear derivative at
the same positive order. It uses the restriction square for the rank equality
already present in the mirabolic derivative, then the published positive-order
definition of the general-linear derivative. No exactness or product theorem
is assumed. The result includes the top derivative and the rank-one source,
without defining a mirabolic group of source rank zero.

These are derived compatibility laws for the existing constructors, rather
than new assertions from the literature. They do not prove any positive-order
Leibniz filtration, tensor-commutation theorem, or mixed-product formula.

## Import and mathematical dependency audit

The only direct project import is `Derivative.Homogeneity`. At Library base
`b22e185743f7c318f709e14e422801f4360105d5`, the complete recursive project
import closure has 55 modules, including this new entry. The exact list is:

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
Langlands.Representation.Derivative.RankCastCompat
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

Mathlib and Lean supply categories, equality elimination and the underlying
representation, module, matrix and topological constructions. The proof terms
here use only equality elimination, identity-functor laws, whiskering of a
natural isomorphism, the published rank equation, and the positive-order
definition of the derivative. In particular, the imported `Homogeneity`
module's level and homogeneity assertions are not proof hypotheses.

| Inherited condition or exclusion | Check for this pair |
| --- | --- |
| Actual functors and natural maps; independent field and carrier universes | All four constructions are natural isomorphisms between composites of the unchanged smooth functors, at independent `uF,uV`. Nothing is proved merely objectwise. |
| All boundary ranks and valid orders; arbitrary carriers | General-linear rank transport allows order zero and rank zero. Mirabolic derivative orders are positive and bounded by `n+1`, including `n=0` and top order. No `P_0`, chosen vector, finite dimension, admissibility, genericity or finite length is assumed. |
| Accepted general upstream inputs; no conditional consumer replacement | Only existing actual constructors and their definition-level laws are used. No exactness, product filtration, tensor commutation or positive-order derivative theorem is assumed. |
| Segment derivative, existence, Jacquet and exponent formulas; analytic classification and Ze80 segment formulas or criteria | No segment module is in the closure and no such conclusion occurs in the proof terms. |
| Unlinked, linked or juxtaposed segment structures, reducibility, reverse quotients, adjacent swaps, two-segment commutation, gluing and ordered socle existence or exhaustion | No corresponding module is imported and none of these conclusions is a proof input. |
| Special-head criterion, generic segment product uniqueness, multisegment exhaustion, strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | No head, socle, multisegment, classification or exhaustion result supplies an input. |
| Square-integrable Langlands classification, square-integrable or regular exhaustion, and forward special essential square-integrability | No square-integrability or classification module is imported; the proofs are the equality and functor laws described above. |
| Two-supercuspidal nonadjacent irreducibility and full-product structure/assembly; no consumer proving its own upstream input | No supercuspidal or product-consumer result is imported or used. |
| Irreducible, Levi-cuspidal and supercuspidal Whittaker finiteness, all-character single-block finiteness and dependent mirabolic finite length | The two Whittaker imports construct characters, functionals and models. They contain no prohibited finiteness result; no finiteness or mirabolic finite-length input is used here. |
| Preserve the target and imported Lean/Markdown pairs | Only `RankCastCompat` is new. The target and every imported pair remain unchanged. |

A recursive import scan and a bounded text scan of all 55 project modules
found no excluded consumer module or named excluded conclusion. The complete
mathematical inputs are the elementary constructor laws listed above, so
none of the excluded conclusions enters transitively through the new proofs.
This pair establishes compatibility laws only and does not discharge the
all-rank Leibniz assertion.
