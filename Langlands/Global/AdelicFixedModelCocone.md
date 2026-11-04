# Full-adele cocone for a fixed initial arithmetic model

This derived construction continues the actual system in
`AdelicFixedModelSystem`, implementing the comparison map in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
equation (3.5.1), printed p.6. The registered source identifier is
`conrad-2011-weil-grothendieck-adelic-points`.

For arbitrary fields `k` and `F` with a `k`-algebra structure, or for a number
field `K`, the actual full adele ring is an algebra over the fixed `S`-integer
ring through the original `S`-level diagonal followed by its subring inclusion.
Every level at `T` containing `S` maps to this algebra by its literal subring
inclusion. The scalar maps commute by evaluation, and these inclusions form
the canonical algebra cocone. All number-field infinite factors are retained.

For any actual scheme `X` over the fixed integer base, the canonical comparison
maps the type colimit of its stage points to its points on the full adele ring.
On each stage its underlying scheme morphism is exactly precomposition with
the spectrum of the actual coefficient inclusion. The full-adele point topology
is final from the previously constructed stage topologies, which are transported
from the original pulled-back arithmetic models. No finite-type, separatedness,
affineness, perfectness, finiteness of constants, or nonempty-`S` premise is used.

`adelicLevelIndexEnlarge` sends a finite set `T` to `S` union `T` and is monotone.
It supplies an elementary enlargement for the subsequent cover argument.
This unit constructs the cocone and point comparison. Its algebra-colimit
universal property, point bijectivity, generic-fiber identification, independence
of the model, and topological properties beyond the defining final topology
remain separate obligations.
