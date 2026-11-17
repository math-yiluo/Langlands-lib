# Successive lifting of actual adic Hom families

This internal reduction implements the homomorphism-lifting recursion in
SGA 3, Exposé IX, Corollaire 7.3 (Gille–Polo recomposed edition, 2009,
p.59, original margin p.72; source `sga3-expose-ix-gille-polo-2009`).
The infinitesimal input remains the explicitly assumed proposition
`MultiplicativeTypeInfinitesimalLiftStatement`.

`evaluate_eq_iff_baseChange_eq` proves that equality of two relative Hom
families after test-scheme evaluation is equivalent to equality after raw
base change. Evaluation inserts canonical source and target pullback
comparisons, both isomorphisms, so they can be cancelled.

`Adic.transitionRingHom I n` is the actual quotient ring map
`A/I^(n+2) → A/I^(n+1)`. It is surjective and has square-zero kernel.
The kernel is the image of `I^(n+1)` in `A/I^(n+2)`; its square vanishes
because `2(n+1) ≥ n+2`. No completeness or noetherianity is used here.

For any group schemes `H`, `G` over `Spec A`, with `H` of multiplicative
type and `G` smooth, `Adic.step_surjective_of_infinitesimal` proves that
the assumed infinitesimal proposition makes every successive actual Hom
evaluation surjective. The proof applies the nilpotent-surjection adapter
to the square-zero quotient map, after base change to level `n+1`.
It transports the supplied level-`n` homomorphism through the canonical
pullback comparisons, lifts it, and cancels those comparisons in the
evaluation formula.

`Adic.first_quotient_surjective_of_infinitesimal` further assumes that
global Hom restriction to compatible adic systems is surjective. The
existing dependent-recursion construction builds a system lifting the
prescribed level-zero homomorphism, and the assumed effectivity
algebraizes it. Thus every first-quotient homomorphism lifts globally.
Both infinitesimal lifting and effectivity remain explicit inputs.
