# Reduction of the split semisimple Picard criterion

`Langlands.GroupScheme.SplitSemisimplePicardReductionStatement.{u}` is a
Prop-valued definition asserting the implication

```text
SplitSemisimplePicardGeometricInputsStatement.{u} →
  SplitSemisimpleSimplyConnectedPicardStatement.{u}.
```

This is an internal reduction statement, in every universe `u`. Its antecedent
is precisely the conjunction of the character-lifting and Picard-trivial-cover
statements in `SplitPicardInputsStatement`. Its consequent is the unchanged
published equivalence for every semisimple group over every field with a split
maximal torus, using actual line bundles on the underlying scheme.

The intended reduction follows the source route explained in the two imported
statement modules: semisimple characters vanish; kernel characters detect a
central kernel inside a split maximal torus; and a simply connected group is
isomorphic to a semisimple central cover with trivial Picard group. This module
only states the implication. It proves neither the implication nor either
geometric input, and asserts no unconditional Picard criterion.
