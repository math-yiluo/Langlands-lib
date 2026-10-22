# Laws of algebraic dual maps: proposition target

`Langlands.AlgebraicDualLawsStatement` is a proposition definition
over a commutative ring, a group, and three independently universed modules.
It states six clauses:

1. Pullback evaluates as `dualIntertwining f ell v = ell(f v)`.
2. Duality preserves the identity intertwiner.
3. Duality reverses the order of composition of intertwiners.
4. The dual of an equivalence has the same pullback formula.
5. The canonical algebraic bidual map evaluates as `ell(v)`.
6. Bidual evaluation is natural: double duality of `f` after evaluation at the
   source equals evaluation at the target after `f`.

Each clause is an explicit proposition definition in this same module, in
order: `DualIntertwiningEvaluationStatement`,
`DualIntertwiningIdentityStatement`, `DualIntertwiningCompositionStatement`,
`DualEquivEvaluationStatement`, `BidualIntertwiningEvaluationStatement`, and
`BidualIntertwiningNaturalityStatement`. The selected target is their conjunction;
unfolding these names yields exactly the six formulas above. Naming the clauses
makes them independently reusable and keeps the serialized aggregate target
small. These definitions neither assume nor prove any clause.

There is no topology, smoothness, dimension, admissibility, or freeness
hypothesis. Neither injectivity nor surjectivity of evaluation is asserted.
These are internally derived laws of the explicit constructions, not the
reflexivity or Hom-space isomorphism theorems in Casselman.

The sole project import is the accepted `Dual.Definitions` pair,
artifact `079d7c1a-8b96-4917-997a-536d6954d55b`, version 1. It was independently
accepted and published at Library commit
`10a8e5eac875b7248fff44f875873354d7d3e9e8`, with receipt
`2b7a1194-a2fd-4aad-bbb5-871370bbfa8b`. The effective Lean SHA is
`53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5`;
the paired Markdown SHA is
`bf9972bb15d854ff605ed825fdcdf90734dc924ad0ae33efb6bb4e55a882845a`.

Source context: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, Section 3, page 6, opening paragraphs and the paragraph following
Corollary II.3.3. See [Definitions](Definitions.md) for the precise source file,
construction-field proofs, and prepared environment.
This pair defines a proposition target; it does not prove the laws. A proof
requires a separately bound task against the accepted, currently published target.
