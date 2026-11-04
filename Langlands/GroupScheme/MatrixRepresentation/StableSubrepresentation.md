# Stable subspaces and actual representation subquotients

This module is an internal derivation from actual matrix representations,
all-affine-test intertwiners, finite split coordinates, and linear splittings
over a field. It does not assert an additional structural theorem about
algebraic groups.

For a field `k : Type u`, an actual group scheme `G` over `k`, a finite matrix
representation `ρ`, and a subspace `V` of its coordinate space,
`IsStableSubspace ρ V` means the following. For every commutative test algebra
`A : CommAlgCat.{u} k`, every actual point `x : Spec A → G`, every `v ∈ V`,
and every `k`-linear functional `ℓ : A → k`, applying `ℓ` to the coordinates of
`ρ_A(x)v_A` gives a vector in `V`. Thus invariance is tested over every affine
algebra, including nonreduced algebras.

The companion lemmas show that coefficient extraction commutes with a
constant matrix, that an intertwiner transports those coefficient vectors,
and consequently that both images and inverse images of intertwiners are
stable. For affine `G`, `IsStableSubspace.isStableCoordinates` turns this
condition and split coordinates into `IsStableCoordinates`. It applies the
existing coefficient-separation lemma on an affine model and the existing
extension from that model to all scheme tests. The already constructed
`restrictCoordinates` is therefore an actual representation on the subspace;
`intertwines_restrictCoordinates` gives its inclusion intertwiner on every
affine test.

Intertwiners compose by matrix multiplication. They can be cancelled through
an injective intertwiner because a matrix over a field remains injective after
every scalar extension. The proof compares columns after multiplication by
that injective scalar-extended matrix.

`isSubquotientOf_of_common_quotient` assumes affine `G` and actual finite
representations `ρ`, `σ`, and `π`, with an equivariant surjection
`C : ρ → π` and an equivariant injection `D : σ → π`. Its conclusion is the
existing `IsSubquotientOf σ ρ`. The proof takes the stable preimage
`V = C⁻¹(range D)`, chooses finite split coordinates `B, P` for it, and uses
the actual restricted representation `τ` on those coordinates. A linear
left inverse `L` of `D` defines the quotient matrix `Q = L C B`.
The relation `D Q = C B` proves equivariance by injective cancellation.
Every vector of `σ` lifts through `C` into `V`, which proves surjectivity
of `Q`; `P B = 1` proves injectivity of the inclusion `B`.

The field universe is arbitrary, and empty coordinate sets are allowed.
No smoothness, connectedness, infinitude, characteristic, perfection or
splitness assumption is used. These lemmas do not yet realize a representation
of a closed subgroup as an ambient representation subquotient. That
construction, unconditional semisimplicity reflection, and the host Cartan
generation proposition remain separate obligations.
