# Intertwining-space length bounds along actual filtrations

This is internal algebraic support for the endomorphism argument in Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.5.3
(printed p. 173, PDF p. 179). The construction is derived from the published
`ObjectRepFiltration` interface and Mathlib's additivity of module length in
short exact sequences. Its proof follows the published restriction and descent
method of `Filtration.InvariantBilinear` and `InvariantBilinearBounds`, applied
directly to intertwining maps rather than bilinear forms.

The coefficient field, acting monoid, source carrier and target carrier have
independent universes. No finite dimension, irreducibility, smoothness or
semisimplicity is assumed.

`HomSpace.length ρ σ` is the extended-natural module length over the coefficient
field of the actual space `ρ.IntertwiningMap σ`. `comap` is precomposition,
and `equivLeft` transports that space along an actual equivalence of source
representations. In particular the full invariant subspace has the original
Hom length, while the zero invariant subspace has length zero.

`restrict` restricts an intertwiner to an invariant subspace. `descend` sends an
element of its kernel to the induced intertwiner on the actual quotient; it is
injective because the quotient projection is surjective. The exact sequence
from the restriction kernel to the Hom space to the restriction image gives
`length_le_subrepresentation_add_quotient`. The image injects into the Hom
space of the subrepresentation, and the kernel injects into the Hom space of
the quotient.

`length_filtration_step` applies this inequality to two consecutive steps of
an `ObjectRepFiltration`. The nested lower step is explicitly equivalent to
the original lower subrepresentation. Induction from the zero step to the
full step proves `length_le_sum`, which bounds Hom length by the sum of Hom
lengths of all actual graded quotients.

`length_le_of_single_piece` removes every summand except a supplied grade
under the explicit hypothesis that all other summands vanish.
`exists_smul_eq_of_length_le_one` proves that every intertwiner is a scalar
multiple of any supplied nonzero intertwiner when Hom length is at most one:
nonzeroness makes the length exactly one, hence the Hom space is a simple
module, and that nonzero vector spans it.
`exists_smul_eq_of_single_piece` combines these two implications.

These are conditional algebraic bounds. They do not assert vanishing of any
geometric piece, prove a geometric lemma, or prove the full maximal-Levi
endomorphism dichotomy.
