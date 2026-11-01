# Interface and scope checks for prescribed additive tensor smoothing

This companion supplies internal interface checks for
`NonUnitalTensorSmoothingStatements`. Its provenance is the task's exact
original-action and universe requirements, rather than an additional
mathematical assertion from Renard. The source assertion and its additive
generalization are documented in the principal paired Markdown.

For each of `InverseIdentities`, `Bijectivity`, `EquivalenceData`,
`PrescribedEquivalence`, `Naturality`, `EquivalenceNaturality` and the closed
`TensorSmoothing`, the module checks the entire unapplied signature and an
explicit definitional unfolding. The aggregate unfolding expands every
component, including both existentially quantified equivalences, both map
pins, all pure-tensor formulas and both pairs of entire-map naturality
equalities. The checks use generic independent universes and the assignments
`(uA,uN,uM,uN',uM') = (0,1,2,3,4)` and `(4,3,2,1,0)`. Thus neither order of the
ring, source factors and target factors can be silently identified.

Conditional specialization examples take `TensorSmoothing` as a local
hypothesis solely to check its applications. They obtain its inverse,
bijectivity, prescribed-equivalence and naturality conclusions under the
following original actions:

- Any additive group with the zero original right action, with no
  nondegeneracy or unit law on that group.
- The concrete nonzero right carrier `ℤ` with its zero `ℤᵐᵒᵖ` action and
  the left carrier `ℤ` with its ordinary nondegenerate action. Separate
  examples prove that the right action fails both nondegeneracy and the
  unit law; these examples do not use `TensorSmoothing`.
- A zero right carrier, a zero left carrier, both zero target carriers in
  the actual tensor-map squares, and the zero ring with a zero left carrier.
  Every zero carrier is `PUnit` in the explicitly specified universe. The
  nondegeneracy of a subsingleton left carrier is proved using the zero
  idempotent.
- A possibly nonunital complex algebra, expressed by `[Module ℂ A]`,
  `[IsScalarTower ℂ A A]` and `[SMulCommClass ℂ A A]`. These structures
  occur only on the ring. No `Module ℂ N`, `Module ℂ M`, scalar compatibility
  of either original action or scalar structure on either target carrier
  is assumed.

All tensor carriers, original actions, intertwiners, restrictions and
comparison maps are the published objects imported by the principal
statement. No replacement tensor or scalar wrapper occurs. The examples
verify elaboration and definitional correspondence; they do not prove
`TensorSmoothing`. Its exact mathematical proof remains a separate successor
after independent acceptance and publication of the statement.
