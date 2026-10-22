# The smooth contragredient

Worker 0 defines the smooth contragredient as the smooth part of Mathlib's
algebraic dual action. This construction pair is proposed for independent
definition review.

For a commutative ring `R`, a group `G` with a topology, and an `R`-module `V`,
`SmoothDual rho` abbreviates the subtype of smooth vectors of `rho.dual`.
It inherits its module structure from that submodule. `smoothDualPairing rho`
is the subtype inclusion into the full algebraic dual, viewed as the
`R`-bilinear evaluation pairing with `V`.

For a topological group, `smoothContragredient rho` restricts the algebraic
dual action to this submodule using `smoothPart rho.dual`. Its action is
`(g ell)(v) = ell(rho(g inverse)v)`. The carrier is the smooth functionals,
not the whole algebraic dual. No topology is placed on either module.

`contragredientMap f` restricts the algebraic pullback map to smooth parts, so
an intertwiner `f : rho -> sigma` induces an intertwiner from the smooth
contragredient of `sigma` to that of `rho`.

For smooth `rho`, `smoothBidual hRho` is the canonical intertwiner into its
double smooth contragredient. `SmoothBidualMap rho` is a transparent abbreviation
for the type of intertwiners from `rho` to its double smooth contragredient;
it adds no hypothesis or assertion. Start with the algebraic evaluation map
`V -> V**`, precompose its values with inclusion of the smooth functionals
into `V*`, and use `smoothLift` to restrict the codomain. It evaluates a smooth
functional at the original vector. This construction asserts neither
injectivity nor surjectivity.

Unlike Casselman's opening definition, the first four constructions permit an
ambient representation that is not itself smooth. This is a direct extension
using the already constructed smooth-part operation. The canonical smooth
bidual map explicitly requires ambient smoothness. There is no admissibility,
freeness, local compactness, or characteristic hypothesis.

## Provenance and dependencies

Casselman, Chapter II, Section 3, page 6, opening paragraphs, gives the
inverse-element dual action and defines the contragredient to be the action
on its smooth vectors. The paragraph after Corollary II.3.3 describes reversal
of equivariant maps by duality. The evaluation construction is internal
infrastructure for the bidual map mentioned in Lemma II.3.2; its isomorphism
assertion is not imported or assumed.

- Literature ID: `casselman-2019-smooth-representations`.
- Content SHA:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Revision: June 16, 2019.
- Actual file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

Direct project imports are `Langlands.Representation.Dual.Definitions`,
accepted artifact `079d7c1a-8b96-4917-997a-536d6954d55b`, version 1,
and `Langlands.Representation.Smooth.SmoothPart.Definitions`,
accepted artifact `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1.
Their independent publication commits are respectively
`10a8e5eac875b7248fff44f875873354d7d3e9e8` and
`cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`; current membership and effective
paired hashes have been verified. The smooth-part foundational dependency
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, is accepted and published.
Only this construction pair is included in the definition submission.
The adjacent law statement and proof remain separate, unaccepted drafts.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0
commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The source's compact-open fixed-vector duality and reflexivity results require
additional arguments and hypotheses; those obligations remain separate.
