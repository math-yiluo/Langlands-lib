# First block and genuine tail of a Langlands standard module

Author: Worker 111.

This internal specialization combines `Classification.LanglandsTailDatum`
with `Parabolic.HeadTailProductInduction`. It supplies the structural step
for induction on the block count of a genuine tempered Langlands datum.
No external mathematical result is newly asserted.

For `d` with `h : d.shape.length = k + 2`, the family
`d.headTailStandardFactors h` lives on the exact two-block shape
`d.shape.headTailShape h`. At zero it is the original first twisted block,
with its carrier lifted by `ULift.{uF}`. At one it is the standard module of
`d.tail h`. The latter datum retains the original remaining irreducible
tempered blocks, their real exponents, and their strict decrease.
The field universe `uF` and original block carrier universe `uV` are independent.
Both outer factors have carrier universe `max uF uV`; the tail receives
no additional lift.

The two component formulas are definitional. The family equality
`headTailStandardFactors_eq` follows by cases on the two outer labels.
In its tail case, unfolding the restricted datum's standard module gives
the normalized product of the original twisted tail, as expressed by
`tail_standardModule` in the imported restriction module.

`headTailStandardModuleIso` specializes the actual first/tail product
isomorphism to `T.twistedBlocks d.shape d.blocks d.exponent`.
Its source is definitionally `d.standardModule`. The family equality is
turned into an isomorphism and mapped through the outer normalized induction
functor to identify the target. `headTailStandardModuleEquiv` extracts the
actual complex-linear representation equivalence.

The equivalence acts over the original ambient `GL_n(F)`. Its target is the
actual normalized upper-parabolic product on the displayed head/tail shape.
No ambient rank transport, arbitrary replacement tail, reordered exponent,
or supplied representation isomorphism is an input. No evaluation formula is
asserted for the chosen isomorphism.

This construction proves no Whittaker type, admissibility, finite generation,
L-polynomial existence, divisibility, or product law. Those remain distinct
obligations of the parent Langlands-type L-factor theorem.
