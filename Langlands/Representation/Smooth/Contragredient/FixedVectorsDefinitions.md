# Fixed smooth functionals and restriction

This module defines two linear interfaces over a commutative ring and a
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

Both direct project imports are published constructions:

- `Contragredient.Definitions`, published at
  `933f2719b54fcf01bebb367c9cae56b8d5f17edc`.
- `SmoothPart.FixedVectorsDefinitions`, published at
  `a158df54c354b831c3b158cd0a299f3f78acb9da`.

Their transitive project definitions are the algebraic-dual construction
(`Langlands.Representation.Dual.Definitions`), the smooth-part construction
(`Langlands.Representation.Smooth.SmoothPart.Definitions`), and foundational
smoothness definitions (`Langlands.Representation.Smooth.Definitions`). Both
direct dependencies and the complete ten-file source closure were verified
at `bb596ce619f2174816281f508cce65b3303beeb4`. The local copies match all
published hashes; no project proof is imported.

The first construction specializes the published smooth-part equivalence to
the algebraic dual action, whose smooth part is definitionally the smooth
contragredient. It inherits every inverse and linearity field from that
equivalence. The second composes the underlying functional with the fixed
submodule inclusion; its additive and scalar fields are definitional.
These constructions require none of the averaging or finite-generation
arguments used in the cited source. The adjacent value and naturality laws are
stated in `FixedVectorsStatement` and proved in `FixedVectorsProof`.
Environment: Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
