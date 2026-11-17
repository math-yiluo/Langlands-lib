# Actual special-fibre Hom transport and cover assembly

This derived interface transports actual special-fibre homomorphisms under a
local algebra base change and records the precise final descent reduction.
Let `A → B` be a local map of commutative local rings, and let `H,G` be group
schemes over `Spec A`. The base rings need not be noetherian or complete.

`specialFibreBaseChangeIso_naturality` proves the naturality square for the
actual special-fibre comparison isomorphisms. The implemented proof separates
the inverse composition comparison, the equality of the two residue-field
base maps, and the second composition comparison. Naturality of the two
composition isomorphisms and equality transport give the three squares;
associativity composes them. The equality-transport square is proved by
equality induction. This avoids expanding an equality of entire functors.

`specialHomTransport` first pulls a special-fibre homomorphism from the
residue field of `A` to that of `B`, then conjugates by the canonical
source and target comparisons. Its result is a homomorphism between the
actual special fibres of `H_B` and `G_B`.
`specialHomTransport_baseChange` says that transporting the special fibre
of a global homomorphism gives the special fibre of its actual base change.
`specialHomTransport_eq_iff` identifies equality with this transported map
with the exact commutative special-fibre comparison square, by cancelling
the target comparison isomorphism.

`specialFibre_hom_bijective_of_cover` assumes additionally that
`Spec B → Spec A` is flat, surjective and quasi-compact. It takes two
explicit hypotheses: special-fibre Hom restriction over `B` is bijective;
and each lift over `B` of a transported special-fibre map has a descent over
`A` whose actual special fibre is the original map. These hypotheses imply
that actual special-fibre Hom restriction over `A` is bijective.

For surjectivity, lift the transported special-fibre map over `B` and apply
the supplied descent-existence hypothesis. For injectivity, two global maps
with the same special fibre have the same transported special fibre by
naturality; injectivity of special-fibre restriction over `B` makes their
base changes equal. Faithfulness of pullback under the fpqc cover then makes
the original maps equal.

This is internal content derived from actual pullback-composition
comparisons, residue-field algebra maps and fpqc faithfulness. The last
result is explicitly conditional on the two stated lifting/descent inputs;
it does not supply those inputs, assert adic effectivity, or prove the full
complete-local deformation theorem.
