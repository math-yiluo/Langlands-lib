# Iterated minimal finite free covers

This internal construction iterates the minimal finite free cover from the
companion module over a Noetherian local ring. The syzygy in degree zero is the
given finite module. Each subsequent syzygy is the kernel of its predecessor's
chosen cover, and is finite because the ring is Noetherian. The free module in
degree `n` is the source of the cover of syzygy `n`; its differential is the
cover map followed by the kernel inclusion.

The preliminary lemma `injective_of_surjective_of_minimal_kernel` states that a
surjection onto a projective module is injective if its source is finite and its
kernel lies in the maximal-ideal multiple of the source. A section of the
surjection gives a retraction onto its kernel. Applying this retraction to the
kernel containment and then using Nakayama shows that the kernel is zero.

This is infrastructure for the residue-field lower-bound proof, derived from
Mathlib's module projectivity and Nakayama results. It does not use a regularity
criterion.

The differential squares to zero, its range is exactly the kernel of the cover
in the preceding degree, and that range lies in the maximal-ideal multiple of
the preceding free module. The cover short complex is short exact. Iterating
Mathlib's short-exact-sequence dimension-shifting theorem gives
`HasProjectiveDimensionLT M (n + m + 1)` if and only if
`HasProjectiveDimensionLT (minimalSyzygy R M n) (m + 1)`. In particular, the
bound `HasProjectiveDimensionLT M (n + 1)` makes syzygy `n` projective.
Its minimal cover is therefore injective by the preliminary lemma, so syzygy
`n + 1` is zero (expressed as a `Subsingleton` instance).

The module supplies the successive free modules, differentials and short exact
cover sequences directly, without packaging them as a categorical projective
resolution. It does not yet construct the comparison with the Koszul complex
or prove the residue-field projective-dimension lower bound.
