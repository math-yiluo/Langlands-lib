# Fixed smooth functionals and restriction

Worker 0 defines two linear interfaces over a commutative ring and a
topological group, for any module representation `rho`.

`smoothDualFixedEquiv rho K` identifies the `K`-fixed vectors of the smooth
contragredient with the `K`-fixed functionals of the full algebraic dual,
when `K` is open. Any such functional is smooth, since `K` itself is an open
fixing subgroup. This specializes the general smooth-part equivalence; it
does not require the original representation to be smooth.

`smoothDualFixedRestriction rho K` restricts a `K`-fixed smooth functional to
the submodule of `K`-fixed vectors of `rho`. It is a linear map into
`Module.Dual R (fixedVectors rho K)`. This map is defined for any subgroup:
neither openness nor compactness is needed simply to restrict a functional.

No injectivity or surjectivity of this restriction map is asserted.
Casselman Proposition II.3.1 proves a stronger isomorphism for compact open
`K`, under the source's coefficient and smoothness assumptions, using the
averaging decomposition. The current pair defines that restriction map and
the preliminary smooth/full fixed-functional identification only.

## Source and dependencies

Casselman Chapter II, Section 3, page 6, opening paragraphs and Proposition
II.3.1; also Section 1, page 2, the definition of smooth vectors.
Literature ID `casselman-2019-smooth-representations`, revision June 16, 2019,
SHA `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual original:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
The weaker hypotheses for the constructions are an internal generalization;
they do not transfer the source's isomorphism conclusion.

Both direct project imports are independently published constructions:

- `Contragredient.Definitions`, artifact
  `be3f8221-aa6f-4069-8faa-f04e1f5dc4b7` version 1, published at
  `933f2719b54fcf01bebb367c9cae56b8d5f17edc`, with receipt
  `60084e7c-d793-42be-9a0a-6906ca4a95e9`.
- `SmoothPart.FixedVectorsDefinitions`, artifact
  `8bf36df6-8b13-4713-89e0-7d2ba5aa6824` version 1, published at
  `a158df54c354b831c3b158cd0a299f3f78acb9da`, with receipt
  `51c5f743-c16d-4e28-919b-c64311bd5224`.

Their transitive project definitions are the algebraic-dual construction
`079d7c1a-8b96-4917-997a-536d6954d55b` version 1, the smooth-part construction
`9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` version 1, and foundational smoothness
definitions `665022df-625b-44ae-9dbd-425f6e266bab` version 1. Both direct
dependencies and the complete ten-file effective source closure were verified
current at `bb596ce619f2174816281f508cce65b3303beeb4`. The normal and draft
copies match all accepted hashes; no project proof is imported.

The first construction specializes the accepted smooth-part equivalence to
the algebraic dual action, whose smooth part is definitionally the smooth
contragredient. It inherits every inverse and linearity field from that
equivalence. The second composes the underlying functional with the fixed
submodule inclusion; its additive and scalar fields are definitional.
These constructions require none of the averaging or finite-generation
arguments used in the cited source. This pair is proposed for independent
definition review, with adjacent value and naturality laws retained as drafts.
Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
