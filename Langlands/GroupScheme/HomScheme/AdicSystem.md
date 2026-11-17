# Compatible homomorphisms over adic thickenings

This internal interface expresses the inverse system of actual group-scheme
homomorphisms used in SGA 3, Exposé IX, Théorème 7.1 and Corollaire 7.3
(Gille–Polo recomposed edition, 2009, pp.56–59, original margins pp.68–72;
registered source `sga3-expose-ix-gille-polo-2009`).

Fix any commutative ring `A`, an ideal `I`, and group schemes `H`, `G` over
`Spec A`. `HomScheme.Adic.System I H G` has an actual homomorphism from
`H_(A/I^(n+1))` to `G_(A/I^(n+1))` for each natural number `n`. Its compatibility
field requires equality after evaluation along the next quotient transition.
Evaluation is the existing `HomScheme.evaluate`, which includes the canonical
comparisons between iterated base changes. Thus compatibility compares maps
with the same source and target, rather than relying on literal equality of
iterated pullback objects.

`System.restrict` takes an actual homomorphism over `A` to these restrictions.
Its compatibility follows from the published `evaluate_baseChange` theorem.
`System.ext` and `restrict_injective_iff` give extensionality and identify
injectivity of this restriction map with the usual equality-on-all-thickenings
condition.

`exists_system_of_step_surjective` assumes that every successive restriction
map is surjective, and constructs a compatible system extending any prescribed
homomorphism at level zero. Its proof uses dependent recursion and choice of
one lift at each step. `exists_lift_of_step_surjective` further assumes
surjectivity of `System.restrict`; it algebraizes that system and obtains a
global homomorphism with the prescribed level-zero restriction.

No completeness, noetherianity, smoothness, or multiplicative-type condition
is needed for these constructions. This file proves the formal recursion and
reduction only. It does not prove surjectivity of successive restriction maps
or effectivity of systems for groups of multiplicative type.
