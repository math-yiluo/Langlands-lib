# Dividing split-torus actions and roots by the characteristic

This internal supporting unit extends the split-torus zero-differential
theorem to homomorphisms from a split torus into any affine group scheme.
The base is an arbitrary field `k : Type u`; the target need not be
commutative, smooth, connected or of finite type. The differential is the
actual postcomposition map on the dual-number identity kernels over `k`.

`SplitTorusActionDivisionStatement.{u}` says that any such homomorphism
`f : T → G` with zero differential factors as `[p]` on the original source
torus followed by an actual homomorphism `g : T → G`, for every nonzero
characteristic `p`. In characteristic zero, `f` is zero.

The proof uses the published dominant split-torus image factorization.
Its image inclusion is a closed immersion, so its differential is
injective. It therefore reflects vanishing of the differential of the
factor map. View this factor as a morphism of commutative group schemes
and apply the previously proved split-torus zero-differential theorem.
Composing its factorization, or its characteristic-zero vanishing, with
the actual image inclusion proves the conclusions for the original target.
The source and image are split over the original field; no extension to an
algebraic closure is used.

The additional `IsCentralIsogeny.exists_divided_root` theorem applies this
factorization when an actual central isogeny `q : G → H` kills the
differential of a specified split-torus map `i : T → G`. Both ambient
groups are affine and locally of finite type. A root `χ` of the original
action remains a root after composition with `q`, by the published
nonzero-weight equivalence for central isogenies. The actual root
restriction theorem for split tori then yields a root `ψ` of the divided
action `j : T → H` with `χ = p • ψ`. It retains the equality
`i ≫ q = [p] ≫ j` of actual homomorphisms.

These are internal deductions from the named Library constructions.
There is no embedding or maximality premise on the source map. This unit
does not prove that suitable successive quotients exist, that iteration
terminates, or the arbitrary-field no-torus unipotence target.
