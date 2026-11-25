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

The sole project import is the `Dual.Definitions` pair. It entered the
Library at commit
`10a8e5eac875b7248fff44f875873354d7d3e9e8`, with Lean SHA
`53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5`
and paired Markdown SHA
`bf9972bb15d854ff605ed825fdcdf90734dc924ad0ae33efb6bb4e55a882845a`.

Source context: `casselman-2019-smooth-representations`, content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
Chapter II, Section 3, page 6, opening paragraphs and the paragraph following
Corollary II.3.3. See [Definitions](Definitions.md) for the precise source file,
construction-field proofs, and prepared environment.
This pair defines a proposition target; it does not prove the laws. The
proof is `Langlands.algebraicDualLaws` in `Dual.LawsProof`.
