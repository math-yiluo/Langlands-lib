# Homogeneous quotients from quasi-affine orbit targets

Over an affine scheme `S`, let `G` be smooth and relatively affine, and let
`i : H → G` be a closed subgroup with `H` smooth over `S`. Suppose an actual
map `r : G → Y` into a quasi-affine scheme over `S` has exactly the right-coset
fibers of `H`, on every scheme test. Then an actual homogeneous quotient
exists, smooth over `S` and with quasi-affine underlying scheme.
`quasiAffineQuotientOfQuasiAffineMapKernel` chooses such a quotient.

This is a derived extension of the existing relatively affine orbit-target
constructor. Its separated-target construction already gives an actual
homogeneous quotient with a monomorphic embedding into `Y`. The source is
of finite type over the affine base, so this embedding is locally of finite
type, and the quotient scheme is quasi-compact. Compose the monomorphism
with the canonical open immersion `Y → Spec Γ(Y)`. The composite remains a
locally finite type monomorphism; the quasi-affine form of Zariski's main
theorem makes its source quasi-affine. The published smoothness theorem for
actual homogeneous quotients of smooth groups supplies smoothness over `S`.
All exact coset fibers and quotient projection geometry are retained from
the original construction.
