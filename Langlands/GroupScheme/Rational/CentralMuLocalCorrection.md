# Local Kummer corrections for a central isogeny with roots-of-unity kernel

Let `L/F` be normal and let `M` contain the fields `K` and `L` with compatible
embeddings over `F`. Fix a central isogeny over `F` and an isomorphism of its
scheme kernel with `μ_n`. `LocalKummerCorrection` records a point `x` over `M`
in the source group, kernel points `dσ` indexed by `Gal(M/K)`, a scalar
`a ∈ Kˣ`, and a radical `z ∈ Mˣ`. For the crossed values `Aσ` obtained from the
original cocycle, the inclusion of `dσ` is `x⁻¹ Aσ σ(x)`. The scalar satisfies
`z^n = a` in `Mˣ`, and the `μ_n` coordinate of `dσ` is `σ(z)/z`.

`nonempty_localKummerCorrection` assumes that `M/K` is finite Galois and `M`
is algebraically closed. The projected cocycle must be a coboundary on the
full pullback cover `Spec (K ⊗[F] L)` over `Spec K`. Evaluate its cochain on
the compatible `M`-point of that cover and lift it along the central isogeny.
The projected coboundary equation puts the twisted values in the actual
kernel. Cancelling the inclusion gives their crossed cocycle law.
The `μ_n` coordinate transports the action to units of `M` and ensures the
values have `n`-th power one. Finite relative Hilbert 90 and fixed-field
descent then give the asserted scalar and radical. This is an internal
construction for the correction at the infinite places.
