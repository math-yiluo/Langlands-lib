# All-field assembly of the central additive-subgroup criterion

This internal deduction combines the two characteristic branches
without altering the published `UnipotentWoundCriterionStatement.{u}`.
It applies to every field in the same arbitrary universe as its actual smooth
connected affine unipotent group schemes.

`criterion_of_structural_inputs` has the exact published proposition as its
conclusion. It retains two explicit arguments:
`SeparablyClosedRationalPointStatement.{u,u}` and
`RelativeRoot.CommutativePTorsionVectorFactorStatement.{u}`.
These are prerequisites of the positive-characteristic branch, not results
proved in this module.

The proof installs the geometric hypotheses from the target and uses
`CharP.exists'` to divide fields into characteristic zero and prime
characteristic. In characteristic zero it applies the unconditional
`criterion_of_charZero`, which derives an actual central additive line from
the generated central subgroup and published perfect-field splitness.
In prime characteristic it applies `criterion_of_charP` to the two supplied
prerequisites. That branch retains the nontrivial pointed commutator and power
family, detects a positive-dimensional vector factor, and composes an actual
closed coordinate line with the central subgroup inclusion.

`centralAdditiveLineOfStructuralInputs` chooses an actual subgroup and
inclusion from the equivalence when an affine-line map is nonconstant.
It includes closedness, centrality and natural one-dimensional vector
coordinates on every relative scheme test.

An unconditional all-field proof by this route requires proofs of both explicit
prerequisites; the Library's unconditional proof is `unipotentWoundCriterion` in
`UnipotentWoundCriterionProof`. This assembly adds no premise to, and changes no file of, the
published target.
