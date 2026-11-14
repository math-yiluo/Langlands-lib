# Actual integral Cartan matrices and arbitrary full derivative bases

Let `i : S → G` be an inclusion of an actual split torus into an affine group
over an arbitrary field. Suppose `Ψ` is a supplied affine root system, allowing
rank zero, on a torsor for its reduced real cocharacter space, and that its full
derivative set is the range of the actual root forms.

`relativeDerivativeRootIndexEquiv` identifies all actual relative roots with all
derivative roots by the actual evaluation map. Injectivity follows from
injective rational evaluation and injective character rationalization for a
split torus; surjectivity is exactly the supplied full derivative equality.
`relativeDerivativeRootEquiv_rootVector` shows that the previously constructed
rational span equivalence sends each actual root vector to the corresponding
root of the rational derivative pairing.

For supplied integral normalizer reflection data and finite actual roots,
`relativeDerivativePairingEquiv` upgrades this full-root linear transport to an
equivalence of the assembled actual rational pairing and the rational
derivative pairing. Mathlib's finite root-system equivalence constructor
derives the coroot compatibility. These comparisons use every root, including
multipliable roots; they impose no reducedness hypothesis.

Now let `P` be a supplied reduced integral root datum with
`hP : IsRootDatumOf i P`, and let `b` be any supplied base of `P`.
`integralDerivativeBaseEquiv` identifies `b.support` with the support of any
supplied base `B` of the full rational derivative pairing.
`cartanMatrix_integralDerivativeBaseEquiv` proves exact equality of their
integer Cartan matrices under that equivalence.

The proof first transfers `b` to the assembled actual rational pairing by
`IsRootDatumOf.rationalBase`. It then applies
`RootPairingBaseComparison.rootTransportBaseEquiv` using the full-root
transport above. That comparison chooses a Weyl identification of simple
supports after transporting roots, so `B` need not be the direct image of the
chosen integral base. Its integer Cartan equality composes with the exact
integral-to-rational Cartan equality.

This is an internal consequence of the imported root-form, rational-pairing,
base-transfer and Weyl comparison results. It assumes the affine root system,
the full derivative identification, finite actual roots and the integral
datum and bases. It supplies no existence theorem for these inputs and no
proof of the host local anisotropic affine-diagram theorem.
