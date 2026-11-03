# Finite-map rigidity for a closed subscheme

Author: Worker 1482.

This internal helper is derived from integral incomparability in Mathlib. For
an integral ring map `A → B` with `A` nontrivial and `B` a domain, a following
map `B → C` is injective whenever the composite is injective: its kernel
contracts to zero, and `Ideal.eq_bot_of_under_eq_bot` forces that kernel to
vanish. No domain condition on `C` is required.

The scheme lemma applies this to global coordinate rings of an integral
affine scheme `Y` finite over a nonempty affine scheme `Z`. If `X → Y` is a
closed immersion and `X → Z` is schematically dominant, injectivity on global
sections and integral incomparability make the closed immersion an
isomorphism. These are actual scheme morphisms; no separability, smoothness
or reducedness of a kernel is assumed.

The intended application is to a closed inclusion of tori `T → M` with a
finite map `M → S` for which `T → S` is surjective. The remaining maximality
argument must still produce the factor `M → S`; this helper does not
construct the image of an arbitrary nonsplit torus.
