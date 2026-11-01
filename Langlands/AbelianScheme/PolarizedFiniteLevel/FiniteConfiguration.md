# Rigidity of finite configurations with sparse hyperplane intersections

This internal linear-algebra support unit concerns an indexed finite family
`v : I → V` in a vector space over a field. `HyperplaneBound v q` means that
the kernel of each nonzero linear functional contains at most `q` entries,
counted with their indices. Repeated entries are counted repeatedly.

`HyperplaneBound.exists_avoiding` uses the finite union bound: the union of
`card J` such kernels contains at most `card J * q` entries. If that number
is strictly smaller than `card I`, some entry avoids every kernel.
`HyperplaneBound.span_eq_top` shows that `q < card I` forces the family to
span. A proper span would be contained in the kernel of a nonzero linear
functional, contradicting the bound.

`scalar_of_basis_and_full_support` proves the elementary linear rigidity
step. A map preserving each basis line is diagonal. Applying every basis
coordinate to the image of a vector with all coordinates nonzero shows
that all diagonal scalars equal the scalar of that vector.

`HyperplaneBound.scalar_of_preserves_lines` assumes finite positive
dimension, the hyperplane bound, and
`finrank K V * q < card I`. It selects a basis from the family and uses
the union bound to find an entry with all basis coordinates nonzero.
Consequently every linear map preserving each indexed configuration line
is scalar. Preserving a line is expressed by the equation
`f (v i) = a • v i` for some scalar depending on the index; no action on
projective schemes is assumed or constructed by this theorem.

`HyperplaneBound.pgl_eq_one` applies the result to Mathlib's actual action
of the projective general linear group on the projectivization of
`J → K`, for a nonempty finite coordinate type `J`. The hypothesis
counts the chosen representatives of the indexed projective points and
requires `card J * q < card I`. It lifts a projective group element to an
invertible matrix. Fixing each indexed point says that each representative
is an eigenvector. The scalarity result makes the matrix scalar, so it lies
in the center of the general linear group and its projective quotient
class is the identity. This proves a trivial pointwise stabilizer over
fields; it constructs no projective scheme or group scheme.

The provenance is an internal deduction from Mathlib's finite-set union
bound, a nonzero linear functional annihilating a proper subspace,
basis selection, and basis extensionality. It isolates an elementary step
suggested by the hyperplane estimate in Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third edition (1994), Proposition 7.7,
printed pp.138–139 / one-based PDF pp.151–152. That contextual source is
registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
This unit does not prove the source's torsion-point estimate, stability
criterion, or geometric moduli result.

No bound on actual abelian-variety torsion points, canonical projective
embedding, comparison with abelian-scheme automorphisms, descent over
nonreduced bases, or representability is established here.
