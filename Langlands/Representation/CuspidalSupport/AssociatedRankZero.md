# Associated Jacquet filtration in rank zero

Author: Worker 193. This is the direct rank-zero branch of the existing
`Langlands.CuspidalSupport.AssociatedJacquetFiltrationTheorem`.
The module preserves the published statement and every imported pair.

`associatedJacquetFiltration_rankZero` proves
`AssociatedJacquetFiltrationTheorem.{uF,uV} F T 0` for every prime `p`,
every actual `PadicField.{uF} p`, and every compatible `TopologicalData`.
The field and inducing carrier universes are independent. All inducing
representations permitted by the published proposition are covered; no
irreducibility, admissibility, finite length, finite dimension, or splitting
hypothesis is introduced. The published quasicuspidality and association
hypotheses are accepted by the proof but are unnecessary at rank zero.
This module does not prove the positive-rank branch or the full universal
target, and is a helper for that complete proof contribution.

## Implemented argument

A positive block in a rank-zero shape would give a coordinate in `Fin 0`.
Thus there are no blocks, every Levi is the empty product group, and its
subgroup lattice is trivial. Every representation of this Levi is
quasicuspidal: the premise that a refinement parabolic is proper is false.

The ambient `GL_0` is also a trivial group. The helper
`subsingletonInducedEquiv` sends an actual smooth covariant function to its
value at the identity. Its inverse is the constant function, whose
covariance follows because the inducing group is trivial and whose
uniform open stabilizer is the whole group. The inverse identities follow
by function extensionality. The helper `subsingletonCoinvariantsEquiv`
inverts the actual coinvariant quotient map using the universal lift of
the identity linear map; every relation is zero for the trivial action.

`rankZero_jacquetInductionEquiv` composes those two linear equivalences.
Both the normalized Jacquet action and Weyl transport are representations
of the trivial target Levi, so this is an actual representation equivalence.
This constructs the equivalence for the exact normalized functors appearing
in the published target, without replacing their carriers or definitions.

The private `oneStepFiltration` has the chain `0 ⊆ A`. Its successive
quotient is the actual top subrepresentation modulo the pullback of the
bottom subrepresentation. `oneStepGradedEquiv` identifies that quotient
with `A` by `Submodule.quotEquivOfEqBot` and `Submodule.topEquiv`; it checks
equivariance on representatives using the surjectivity of the quotient map.

There is exactly one permutation of `Fin 0`; its minimality conditions are
vacuous and it conjugates the two trivial Levis. The final proof uses an
actual bijection from `Fin 1` onto **all** minimal conjugating permutations
and composes the graded equivalence with `rankZero_jacquetInductionEquiv`.
It retains that single factor even when the inducing representation is zero.

## Provenance and limits

This is an internal boundary-case argument for the published GL specialization
of Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Corollary 2.13(c), printed p.449/PDF10. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The source's geometric-lemma argument was read directly, but this proof
uses only trivial-group constructions and does not import a geometric-lemma
proof. The published `PadicGeometricLemmaTheorem` covers positive rank and
therefore cannot itself supply this boundary case.

This helper is submitted together with the unconditional theorem in
`AssociatedProof`; its implementation is specific to rank zero.
