# Open loci in affine Weil restriction

This is derived construction infrastructure for the nonaffine Weil restriction
in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Example 4.2, printed pp.9–10, registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source reduces its local comparison to affine open pieces of the Weil
restriction. The construction here supplies restriction of scalars for any
open subscheme of an affine finite-type scheme.

This is a derived construction, rather than a transcription of a construction
given in the paper. Example 4.2 invokes representability from BLR and reduces its
topology comparison to affine open pieces. Here the existing actual affine
Weil restriction and its universal morphism supply an open representing scheme.
Full nonaffine gluing and the local and adelic topology comparisons remain
separate obligations.

The rings `A` and `B` are commutative and lie in any common universe `u`, with
an `A`-algebra structure on `B`. The hypotheses `Module.Finite A B` and
`Module.Projective A B` express that the extension is finite locally free.
The scheme `X` is affine over `Spec B`, with locally finite type structure
morphism; since both schemes are affine this is the usual finite type setting.
There is no field, separability, local-ring or topological hypothesis. The chosen
open subset `U` of `X` can be arbitrary, including empty and nonaffine opens.
No quasi-compactness or finite type conclusion is asserted for this arbitrary
open or its representing scheme.

For a universally closed morphism `π : Z ⟶ W`, a morphism `e : Z ⟶ X`, and
an open `U`, `universallyClosedFactorizationOpen π e U` is the actual open
subset

`W \ π(Z \ e⁻¹(U))`.

The image being removed is closed because `π` is closed and the inverse image
of the closed complement of `U` is closed.
`mem_universallyClosedFactorizationOpen` identifies membership with the condition
that every point of the fibre maps into `U`. For every cartesian square obtained
from `p : T ⟶ W`, `range_subset_factorizationOpen_iff` proves that the image
of `p` lies in this open exactly when the induced morphism from the base change
lands in `U`. The reverse direction uses Mathlib's
`Scheme.exists_preimage_of_isPullback`: two compatible points of schemes lift
to a point of their fibre product. In particular the argument works for every
test scheme `T`, without assuming it affine.

Write `W = affineWeilRestriction A B X`, and let `e : W_B ⟶ X` be the
published actual universal counit. Its projection `π : W_B ⟶ W` is finite,
being a base change of `Spec B ⟶ Spec A`, and hence universally closed.
`affineWeilRestrictionOpenLocus A B X U` applies the preceding construction
to these actual morphisms. `openAffineWeilRestriction A B X U` is the
corresponding actual open subscheme of `W`, equipped with its structure
morphism over `Spec A`.

`ringBaseChange_map_isPullback` proves that the map on base changes of any
relative morphism forms a cartesian square with the first projections. It uses
the canonical pullback squares and cancellation of the right square.
Consequently `range_subset_affineWeilRestrictionOpenLocus_iff` identifies
factorization of `T ⟶ W` through the open locus with factorization of its
actual adjoint `T_B ⟶ X` through `U`.

`openAffineWeilRestrictionComparison` sends a morphism from `T` into the
constructed open to its affine adjoint, lifted into `U`.
`openAffineWeilRestrictionComparison_fac` proves compatibility with the
inclusion `U ⟶ X`. `openAffineWeilRestrictionComparison_natural` proves
compatibility with every morphism of test schemes by composing with this
inclusion, using naturality of the affine comparison, and cancelling the
open immersion. Finally `openAffineWeilRestrictionComparison_bijective` proves
the natural bijection

`Hom_A(T, openAffineWeilRestriction A B X U) ≃ Hom_B(T_B, U)`

for every actual `A`-scheme `T`. Injectivity reduces to that of the published
affine comparison and cancellation of the inclusion into `W`. For surjectivity,
first extend the target morphism along `U ⟶ X`, apply the published all-test
affine bijection, and then lift its inverse through the open locus using the
range equivalence. Cancellation of `U ⟶ X` gives the required equality.
These proofs establish representability of this open-subscheme functor and do
not assume that either `U` or `T` is affine.
