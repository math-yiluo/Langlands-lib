# Nilpotent surjections on actual affine-open sections

This internal prerequisite transports nilpotent surjections through actual
categorical pushouts of commutative rings and specializes that transport to
sections on affine opens of the actual relative schemes. All rings and schemes
lie in an arbitrary common universe `u`. The base `k` is an arbitrary commutative
ring, and `f : X ⟶ Spec k` is an arbitrary scheme morphism.

A commuting square of ring isomorphisms carries the kernel ideal to its image
under the source isomorphism. Ideal image preserves nilpotence, and the same
square preserves surjectivity. Applying these facts to the canonical tensor
coordinates of an actual pushout proves `nilpotentSurjective_of_isPushout`.
The source coordinate uses the identity pushout, so the tensor map is precisely
the scalar extension of the original surjection. The tensor surjectivity and
kernel nilpotence lemmas in `InfinitesimalTensorNilpotence` supply the result in
those coordinates. `pushoutSpecHomeomorph` packages the resulting actual
spectrum arrow as a homeomorphism of underlying spaces.

For a surjective `k`-algebra homomorphism `b : B →ₐ[k] C` with nilpotent kernel,
`relativeRestriction_appTop_nilpotentSurjective` considers the actual relative
map `i : X_C ⟶ X_B`. For every affine open `W` in `X_B`, it proves that the
actual global sections map of `i ∣_ W` is surjective and has nilpotent kernel.
The map `i` is affine because it is the base change of `Spec b`, so its inverse
image of `W` is affine. Pasting the open restriction square with the relative
projection square gives a cartesian square with these two affine schemes and
`Spec C`, `Spec B`. Its global sections form a ring pushout. Naturality of
`Scheme.ΓSpecIso` first transports the original hypotheses on `b` to the
global sections map of `Spec b`; the pushout lemma then gives the conclusion.

For the actual relative square associated to a categorical algebra pullback
`R → A`, `R → B`, `A → C`, `B → C`, the lemma
`rightRestriction_appTop_nilpotentSurjective` proves the same two properties for
the exact `InfinitesimalAffineOpenSquare.rightRestriction` on every affine open
`U` of `X_R`. The inverse image of `U` in `X_B` is affine. Apply the preceding
lemma there, then use the square's commutativity to identify the common source
open with its inverse image in `X_C`. The helper
`resLE_appTop_nilpotentSurjective` transports the sections property to this equal
open, retaining the specified `resLE` morphism and hence the exact right
restriction.

This is an internal derivation from the tensor nilpotence and pushout-coordinate
lemmas, the actual relative projection squares, and Mathlib's affine cartesian
global-sections pushout theorem. No flatness, field, properness, or finiteness
assumption is used for these nilpotent-surjection conclusions. The separate
claim that the whole restricted sections square is a ring pullback retains its
flatness hypotheses in `InfinitesimalAffineOpenSquare`. Global effectivity,
full faithfulness, and the equivalence of the specified Picard comparison
remain obligations of the host infinitesimal-gluing task.
