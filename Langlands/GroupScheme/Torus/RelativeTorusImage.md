# The image torus of a relative torus homomorphism

Let `T` be a relative torus over a scheme `S` and let `G` be an affine group
scheme locally of finite type over `S`. The theorem `exists_factorization`
factors a homomorphism `T ⟶ G` through its schematic image. This image is a
relative torus, its inclusion in `G` is closed, and the projection from `T`
is flat, surjective and locally of finite presentation.

The homomorphism is quasi-compact because `T` is affine over `S` and `G` is
quasi-separated over `S`. On a refined étale splitting cover of `T`, the
local factorization theorem gives split tori as images. The scheme
comparisons on these charts give flatness and surjectivity of the canonical
projection by descent. The schematic image then inherits its group law from
`G` and commutativity from `T`.

The chart comparisons preserve the two image inclusions in the pullback of
`G`. Cancelling the closed inclusion identifies the unit and multiplication
on the two sides, so the comparisons are group-scheme isomorphisms. This
exhibits the canonical image as a relative torus on the same étale cover.
Both tori are smooth over `S`, and the triangle over `S` gives local finite
presentation of the projection.

This internal theorem combines the Library's local split-torus factorization
and schematic-image constructions. The affine, locally finite type target
is the hypothesis used in the local coefficient argument.
