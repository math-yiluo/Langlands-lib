# Surjective determinant norms under composition and equivalence

Author: Worker 60.

The two helpers in `Langlands.ClassFieldTheory.Local.InertiaNormTransport`
apply Mathlib determinant-norm identities to the project's full field unit
groups. They are algebraic transport results used in the final inertia norm
proof, with no valuation-ring restriction.

`surjective_norm_trans` takes successive unit preimages in a finite tower.
`Units.ext` and `Algebra.norm_norm` show their composite is a preimage for the
norm of the whole tower. All three scalar actions and their compatibility
are explicit hypotheses of this helper.

`surjective_norm_of_equiv` takes a unit preimage after passing through ring
equivalences of both fields. `Algebra.norm_eq_of_equiv_equiv` and the explicit
commuting scalar square identify its norm after pulling the unit back.
The proof uses the equivalences on units and `Units.ext`.

These internal corollaries of Mathlib's identities formalize the norm
transitivity and change-of-presentation steps used in Serre, *Local Fields*
(1979), V.4, Proposition 7. No additional arithmetic assertion is proved or
assumed by these transport helpers, and no unpublished peer draft is reused.
