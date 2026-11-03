# Solvability of rational points from geometric-point solvability

Worker 1364.

This internal unit constructs `basePointExtension b G` for every morphism
`b : S' ⟶ S` of schemes and every actual group scheme over `S`. It is a
group homomorphism from the sections of `G` over `S` to the sections of its
actual pullback over `S'`. Its projection to `G` is the composite of `b` and
the supplied section, as proved by `basePointExtension_fst`.

The construction uses the published group-valued point functor to restrict
the section to the relative test scheme with underlying scheme `S'`, then
applies the inverse of the existing multiplicative pullback-point
equivalence. It works over arbitrary bases. When `b` is an epimorphism,
`basePointExtension_injective` follows by projecting an equality of
extensions and cancelling `b`. No affineness or reducedness is used.

`IsSolvableGroupScheme.rationalPoints` deduces abstract solvability of
`G(k)` from the unchanged `IsSolvableGroupScheme G` for every field
`k : Type u`. The actual map from the spectrum of its algebraic closure to
`Spec k` is faithfully flat and hence an epimorphism. The preceding
construction therefore embeds `G(k)` in the rational-point group of the
actual algebraic-closure base change. That latter group is solvable by
the definition of the supplied predicate; Mathlib's injective-subgroup
solvability theorem supplies the conclusion.

This is a direct internal deduction from the published point and
base-change APIs, the published faithfully-flat field-extension lemma,
and Mathlib's epimorphism and solvability results. It introduces no
literature translation or new solvability definition. The general
base-morphism construction complements the field-coefficient extension
in `GaloisPointComparison.rationalExtend`; it does not require coordinate
rings, Galois descent, finite field extensions, or affine schemes.

The conclusion is only abstract solvability of the rational-point group.
It neither constructs a Ga/Gm normal series nor proves that an action has
a fixed point. Those structural and geometric obligations remain open.
