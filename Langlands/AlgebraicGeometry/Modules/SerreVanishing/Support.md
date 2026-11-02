# Smaller support for section multiplication

This internal helper proves that multiplication by a section is an isomorphism
on its actual trivialization open. It transports restricted maps to pullback,
uses the natural invertible pullback tensor comparison, and transports back.
Thus tensoring two maps invertible on an open preserves invertibility there.
The definition of `twistMul` then gives the desired local isomorphism.

`SectionErrorsLT N s G e` asserts the support-height bound `e` for both the
kernel and cokernel of multiplication by `s` on `G`. If `G` vanishes off an
irreducible closed set `T` of height at most `e`, and the trivialization open
of `s` meets `T`, both errors have this bound. Tensoring with the rank-one
module `N` preserves stalk support, so source and target vanish off `T`.
The Library's irreducible support-drop lemmas apply to the local isomorphism.

For an ample line bundle, choose a point in `T` and use the definition of
ampleness to obtain a section of a positive tensor power with affine
trivialization open containing that point. The preceding argument gives
smaller support for both errors. No generic-point, smoothness, reducedness,
or section non-zero-divisor hypothesis is used.

These are derived support and tensor facts for the authorized Serre vanishing
proof. They do not use or prove `SectionKillingStatement`.
