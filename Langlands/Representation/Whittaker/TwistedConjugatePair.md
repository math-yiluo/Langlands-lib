# Squared-norm coefficient products for a twisted contragredient pair

This internal construction transports the conjugate-coefficient identity to
an actual pair of representations related by a character twist.

Let `χ` and `α` be characters of a topological group `G` with values in
`ℂˣ`, both with open kernels. Suppose that compact open subgroups are cofinal among
open subgroups, `σ` is admissible, and there is an actual representation
equivalence

`e : twist χ π ≃ smoothContragredient σ`.

`twistedDualTransportEquiv` constructs an equivalence from `σ` to

`twist (χ⁻¹ * α) (smoothContragredient (twist α π))`.

Its proof uses the published admissible smooth-bidual reflexivity theorem,
dualizes `e`, and applies the published smooth-dual twist equivalences.
Twisting the smooth dual of `twist α π` back by `α` cancels its inverse twist.
These are actual equivalences of representations; no identification of
isomorphism classes is used.

For `exists_twisted_conjugate_functional`, let `N` be a subgroup, `θ` a unitary
complex character of `N`, and assume that `χ` and `α` are trivial on `N`.
Suppose also that `τ = twist α π` is admissible and carries an invariant
positive Hermitian form `b`. For any nonzero `θ`-equivariant functional `ℓ` on
`π`, the theorem produces a nonzero `θ⁻¹`-equivariant functional `m` on `σ`.
The functional `m` is fixed independently of the vectors. For every vector
`v` of `π` there is a vector `w` of `σ` such that, at every group element `g`,

`Wπ(ℓ,v)(g) * Wσ(m,w)(g) = χ(g)⁻¹ * ‖Wτ(ℓτ,v)(g)‖²`,

where `ℓτ` is the published twist transport of `ℓ`, and the real squared norm
is embedded in the complex numbers.

The proof first constructs the inverse-character functional on the actual
smooth dual of `τ` using `hermitianDualFunctional`. It twists this functional
by `δ = χ⁻¹ * α` and pulls it back along `twistedDualTransportEquiv`.
Nonzeroness follows from the nonzero Hermitian-dual functional and
surjectivity of the equivalence. For the paired vector choose the inverse
image of `b.toSmoothDual v`. Equivariance gives the second coefficient as
`δ(g) * conj(Wτ(ℓτ,v)(g))`. The first coefficient satisfies
`Wτ(ℓτ,v)(g) = α(g) * Wπ(ℓ,v)(g)`. Their product is therefore the stated
inverse-character multiple of the squared norm.

The provenance is the composition of the imported duality, scalar-twist,
functional-pullback and conjugate-coefficient constructions. The group and
both carriers have independent universes, and no topology or norm is
assumed on either carrier. This is a pointwise identity. It does not assert
convergence or nonvanishing of an integral or a residue.
