# Stable freeness after localization of a module of finite projective dimension

This internal auxiliary result is developed for the proof that regular local
rings are factorial. It concerns a commutative Noetherian local ring `R`, a
finite `R`-module `M`, an integer `n ≥ 0` bounding its projective dimension, and
an arbitrary multiplicative submonoid `S`. If the localization of `M` is
projective over `Localization S`, it is stably free.

The induction theorem
`moduleCat_localizedModule_isStablyFree_of_hasProjectiveDimensionLE` uses
Mathlib's bundled, universe-preserving localized module. The ring and module
belong to the same arbitrary universe.

The public wrapper
`isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE` permits any
model of the localized module, including a model in a different universe, as
long as its scalar ring is `Localization S`. It transports projectivity and
stable freeness along the canonical linear equivalence of localized modules.
The canonical version is
`localizedModule_isStablyFree_of_hasProjectiveDimensionLE`.

Finally,
`localizedModule_free_of_invertible_of_hasProjectiveDimensionLE` assumes
invertibility of the localized module and concludes freeness. Invertibility
supplies projectivity, the canonical theorem supplies stable freeness, and
Mathlib's `Module.free_of_isStablyFree_of_invertible` proves freeness.

The proof is an internal algebraic derivation using Mathlib's exactness,
projective dimension and stable freeness APIs. It does not assert that all
finite modules over a regular local ring have finite projective dimension.
That input is a separate obligation in the factoriality proof.

The implementation inducts on `n`. At `n = 0`, `M` is projective and hence
finite free over the local ring; localization preserves freeness. At the
successor step, a finite free surjection `P → M` has finite kernel `K`, whose
projective dimension is at most `n` by dimension shifting. Localization
preserves the resulting short exact sequence. Its projective quotient splits
the sequence, so `P_S` is isomorphic to `K_S × M_S`. In particular, `K_S` is
projective and the induction hypothesis applies.

For completeness, if `K_S × Q` is finite free with `Q` finite free, then the
product `M_S × (K_S × Q)` is free: permuting its factors identifies it with
`P_S × Q`. This supplies the finite free complement required for stable
freeness. The private helper implements this permutation argument.
