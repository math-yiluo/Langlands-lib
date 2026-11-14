# Rational simple bases from supplied actual integral root data

For an inclusion `i : T → G` of a split torus into an affine group over an
arbitrary field, let `P` be a supplied reduced integral root datum with witness
`hP : IsRootDatumOf i P`, and assume that the actual relative roots are finite.
For every supplied simple base `b` of `P`, `IsRootDatumOf.rationalBase` constructs
a base of `hP.relativeRootReflectionData.rootPairing hT hfinite`, the rational
pairing on the actual relative-root span and its rational dual.

`relativeRootEquiv` identifies the full integral index set with all actual
relative roots. Its forward map is the integral root map and its inverse is the
existing `relativeRootIndex`. The support of `rationalBase` is exactly the image
of `b.support` under this equivalence. `rationalBaseSupportEquiv` restricts the
same equivalence to the two simple supports.

The construction applies the internal `IntegralRationalRootBase` transfer with
common ambient space `ℚ ⊗[ℤ] characterLattice T`. The source realization sends
a character to `1 ⊗` that character; its injectivity follows from splitness of
the actual torus. The target realization is the inclusion of the actual
rational root span. These realizations agree on every root. No assumption that
all rational characters lie in the root span is needed, so central directions
are allowed. The previously assembled rational pairing is a finite
crystallographic root system; the generic transfer derives reducedness and
constructs the root and coroot base axioms.

`rationalRootPairing_pairing` evaluates the assembled coroot functional on an
actual root vector. The inverse index identity identifies the supplied coroot,
and `hP` identifies the lattice pairing with `P.toLinearMap`. Thus every
rational root-coroot pairing is the corresponding integral pairing cast to
`ℚ`. `cartanMatrix_rationalBaseSupportEquiv` then proves exact equality of the
integer Cartan matrices in the original index order.

This is an internal application of the imported actual reflection assembly and
integral-to-rational base transfer. It asserts neither existence of the supplied
root datum nor existence of a simple base, maximality of the torus, an apartment
comparison, or the host local anisotropic affine-diagram theorem.
