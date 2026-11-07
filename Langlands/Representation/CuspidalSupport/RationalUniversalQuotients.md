# Generation by the actual norm-kernel compact induction

This internal construction uses the published full restriction, compact induction,
carrier lift, unramified characters and inertia relation. On the complete norm
kernel every unramified character is one, so the up/down carrier equivalence
identifies the restricted original representation with the restriction of each
unramified twist of its lifted base. Composing with an inertia isomorphism and
applying the open-subgroup coset sum produces an actual surjection from the
compact induction to that object: its composite with the subgroup unit is the
surjective restricted equivalence. No irreducibility of the base is used.

The field and original carrier universes are independent. All orbit targets and
the compact induction have carrier universe `max uF uV`.

`rationalNormKernelInertiaQuotient` chooses such an actual quotient morphism;
`rationalNormKernelInertiaQuotient_surjective` proves its surjectivity. These
constructions are derived from the imported algebraic and open-subgroup APIs.
They assert no block membership or projectivity of the inducing object, and do
not prove the host small-progenerator statement. Faithful integer Hom is a
separate argument using projectivity and irreducible-subquotient detection.
