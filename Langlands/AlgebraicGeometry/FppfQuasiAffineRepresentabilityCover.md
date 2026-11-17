# Quasi-affine representability from finite affine fppf covers

Let `S` be affine and let `F` be an actual fppf sheaf of sets on all schemes over
`S`. Suppose a finite jointly surjective family `Bᵢ → S` consists of flat maps
locally of finite presentation, with each `Bᵢ` affine. If each full restriction of
`F` is represented by a quasi-affine scheme over `Bᵢ`, then `F` is represented
by a quasi-affine scheme over `S`. `quasiAffineModelOfFiniteCover` chooses that
model and retains its full Yoneda representation.

This is derived infrastructure. The proof forms the finite affine coproduct of
the covering schemes and restricts the sheaf to it. The standard slice-functor
composition isomorphisms identify the restrictions to the coproduct summands
with the given representations. `LocalRepresentation.exists_representation`
glues these over the open cover by summands. Uniqueness of full Yoneda
representations identifies each pullback of the glued scheme with its given
quasi-affine model. `QuasiAffineCoverDescent` shows the glued scheme is
quasi-affine. The coproduct map is flat, surjective and locally of finite
presentation; both bases are affine. The single-cover construction
`FppfQuasiAffineRepresentabilityDescent.quasiAffineModel` then descends the
glued representative to `S`.
