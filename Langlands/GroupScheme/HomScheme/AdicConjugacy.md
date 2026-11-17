# Algebraizing compatible conjugating points

This internal reduction implements the final passage to the complete ring in
the proof of SGA 3, Exposé IX, Corollaire 7.3 (Gille–Polo recomposed edition,
2009, p.59, original margin p.72; registered source
`sga3-expose-ix-gille-polo-2009`).

`conjugationFamily_constantPoint` identifies conjugation by the constant
family of a global point with actual base change of the globally conjugated
homomorphism. It uses the existing point adjunction and the published
base-change compatibility of inner automorphisms.
`conjugationFamily_one` states that conjugation by the identity is trivial.

`Adic.ConjugatorSystem I f f'` packages actual points on the adic thickenings,
their transition compatibility, the identity at level zero, and their
conjugacy equations for the two fixed global homomorphisms.

For group schemes `H`, `G` over `Spec A`, assume `A` is complete and separated
for an arbitrary ideal `I`, `G` is affine over `Spec A`, and restriction of
global homomorphisms to actual adic systems is injective.
`Adic.exists_conjugator_of_compatible_points` takes compatible points
`g_n ∈ G(A/I^(n+1))`, with `g_0 = 1`, conjugating the restrictions of two
fixed global homomorphisms. It produces a global point, reducing to the
identity at level zero, which conjugates the original homomorphisms.

The proof first applies `AdicAffinePoints.existsUnique_over_adic_lift` to
the actual morphisms over `Spec A`. Compatibility ensures a single global
point with precisely those reductions. The constant-family identity then
identifies the reductions of its global conjugation, and the assumed
injectivity of `Adic.System.restrict` gives global equality.
`Adic.ConjugatorSystem.exists_global` applies this result directly to a
packaged system.

`Adic.exists_conjugator_of_step_lifting` replaces a pre-existing compatible
family by the assumption that each conjugating point can be extended one
level while remaining a conjugator. Starting at the identity and using
dependent recursion, it constructs the family and applies the preceding
result. The step-lifting assumption and Hom injectivity remain explicit.
No smoothness, noetherianity, or multiplicative-type condition is used in
this formal reduction; those hypotheses enter the missing mathematical
inputs that establish the step-lifting and injectivity assumptions.
