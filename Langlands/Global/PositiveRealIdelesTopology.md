# Closed embedding of the actual positive scalar ideles

Worker 112.

This is an internal topological consequence of
`Langlands.Global.PositiveRealIdeles`, the published continuous local idele
projections, and Mathlib's norm and closed-retract APIs. It supplies a
closedness fact needed when positive-real groups are used in adelic quotients.
It assumes only an arbitrary number field `F`, with its actual adelic and
idele topologies already fixed by the imported constructions.

`localNorm F w` applies the ordinary, unweighted nonnegative-real norm to a
unit of the actual archimedean completion at `w`. Applying the units functor
to the norm homomorphism gives a homomorphism to `ℝ≥0ˣ`. The norm is continuous,
and the units topology tracks both a value and its inverse, so this is a
continuous homomorphism. `normRetraction F w` composes it with the existing
continuous local idele projection.

The scalar-component formula of the preceding module proves
`normRetraction_full`: at every infinite place the local norm of the inserted
positive real is that same positive real. Thus each infinite place gives a
continuous left inverse to `full F`. A number field has at least one infinite
place, including when it has no real places. Choosing any such place and
applying Mathlib's closed-retract theorem in the Hausdorff actual idele group
proves `isClosedEmbedding_full`. In particular its actual range is closed.
The required Hausdorff instances are derived from the product of the actual
archimedean completions, the actual restricted product at finite places, and
the existing units topology; Hausdorffness is not an additional hypothesis.
The choice is used only in the proof; no place is chosen in the definition
of the scalar map or its image.

`isClosedEmbedding_full_pi` is the product of these closed embeddings for
any index type, with the existing product topologies. Empty index types are
allowed. It does not install a topology on affine points of a general torus;
transport to that topology requires a proved continuous coordinate equivalence.

The unweighted local norm used as a retraction is distinct from the normalized
global idelic absolute value. The preceding identity
`IdeleAbsoluteValue.full F (full F x) = x ^ Module.finrank ℚ F`
is preserved. No Haar measure, finite covolume, central split-torus selection
or reduction theorem is asserted.
