# Irreducible constituents at the prescribed standard level

This internal adapter combines the published actual normal-level fixed-vector
criterion, prescribed-level induction generation and fixed-Levi rational
inertia comparison. It does not prove VI.9.4 or the full Bernstein inertial
visibility comparison. The ambient field universe and coefficient-carrier
universe remain independent.

The theorem
`fixedVectorGenerated_standardInduction_of_irreducible_of_nontrivial_fixedVectors`
is unconditional under its displayed geometric level hypotheses. The compact
open subgroup K is contained and normal in the compact subgroup K₀, the minimal
standard Iwasawa factorization holds with K₀, and K has the stated standard
basis-member property for the chosen standard parabolic. If the coefficient
representation of the literal standard Levi is irreducible and its actual
normalized induction has a nonzero K-fixed vector, that induction is generated
by its K-fixed vectors at this same K. No admissibility or finite-length premise
is imposed. The normal-level criterion first gives a nonzero coefficient vector
fixed by the literal inverse image of K in the Levi. The irreducible generation
criterion makes these coefficient vectors generate. The published prescribed
induction-generation theorem then proves the conclusion.

`standardConstituentFixedVectorVisibility` is the level-dependent property
that every irreducible actual constituent of induction of irreducible
coefficients has nonzero K-fixed vectors if and only if the induction does.
Its theorem `standardConstituentFixedVectorVisibility_of_subquotientGeneration`
retains `StandardFixedVectorSubquotientGenerationStatement` explicitly, in
carrier universe `max uF uV`. It also requires the displayed level hypotheses,
including the standard basis-member property along every standard parabolic.
In the forward direction, the first theorem generates the induction, VI.9.4
generates its actual constituent, and irreducibility supplies a nonzero fixed
vector. In the reverse direction, compact-open exactness transfers a nonzero
fixed vector from the actual subquotient to the induction.

Finally,
`nontrivial_fixedVectors_constituents_iff_of_rationalInertiaRelated`
assumes this constituent visibility property for one fixed standard Levi.
Transport through its actual rational-point homeomorphism preserves coefficient
irreducibility. Apply the property to each coefficient, and compose with the
published equivalence of induced fixed spaces for full rational inertia.
This proves the comparison for actual constituents of these two inductions.
The theorem does not infer any ambient induction isomorphism or support
transport from an association between different Levis.

These are derived Lean consequences of the imported declarations. They are
intermediate results for VI.10.6(iii)–(iv); the host proposition remains open.
