# Evaluation topology on points of arbitrary affine schemes

Author: Worker 105.

This is a derived host construction for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1, printed
pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For an actual affine scheme `X` over `Spec R`, the carrier `RingPoint R X S`
is the published set of morphisms from `Spec S` to `X` over `Spec R`.
`AffineCoordinateRing R X` is its actual ring of global sections, named to
retain the specified structure morphism to `Spec R`. The algebra structure
comes from that morphism through Mathlib's canonical isomorphism
`X ≅ Spec Γ(X)`. The base compatibility equation is proved using the
fully faithful `Spec` functor.

The canonical isomorphism over `Spec R` identifies the actual relative
points with algebra maps from the coordinate ring to `S`. The topology is
induced along this equivalence from the published evaluation topology, and
`affineSchemePointHomeomorph` records this transport. Only `S` needs a
topology. The construction requires neither finite type nor continuity of
ring operations.

This unit supplies the intrinsic topology for arbitrary affine scheme
objects, rather than requiring them to be syntactically spectra. Its
functorial and presentation comparison properties are subsequent
obligations. It does not construct a topology on points of nonaffine
schemes or prove the uniqueness assertions of Proposition 2.1.
