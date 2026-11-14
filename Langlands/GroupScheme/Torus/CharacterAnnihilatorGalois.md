# Full character annihilators and Galois transport

This internal construction connects actual integral character submodules
to full subgroup functors. Its inputs are the Library's character evaluation
on every relative test scheme, detection of split-torus points by those
characters, and canonical Galois transport of points and characters.
It supplies no numbered type-D cover or computation of its character image.

For a commutative group scheme `T` over the spectrum of a domain `k`,
`characterLattice.annihilatorSubgroupFunctor T L` assigns to each test
scheme `U` the points `x` on which every actual character in the integral
submodule `L` has value `1`. Values are global units on `U`. Character
evaluation preserves point multiplication and inversion, and its naturality
under every morphism of test schemes proves that these subgroups form a
subgroup functor. The definition does not assume that `T` is a torus.

For a homomorphism `f : T.toGrp → Q.toGrp` into a split torus,
`range_kernel_eq_annihilator` identifies the full range of the actual
kernel inclusion with the annihilator of the integral range of
`characterLattice.comapHom f`. A kernel point kills every pullback
character by functoriality. Conversely, if every such character is
trivial, the character model of the split target identifies its image
with the identity on that same test scheme. No splitness assumption is
needed on `T`, and no saturation of the image is taken.

Let `K/k` be any extension of fields in universe `u`, and let `T` be
defined over `k`. For a submodule `L` of the actual character lattice
of `T_K`, `descentTransport_annihilatorSubgroupFunctor` proves that
canonical Galois transport along `σ : K ≃ₐ[k] K` of its full annihilator
is precisely the annihilator of
`L.map (characterLattice.galoisRepresentation k K T σ)`.
Membership in a transported subgroup is membership of the canonically
transported point on the test scheme with its changed `K`-structure.
The published formula `galoisRepresentation_points` equates evaluation
there with evaluation of the transported character on the original
test scheme. Membership in the image submodule supplies exactly the
characters needed in both directions.

It follows that equality of that image submodule with `L` implies
invariance of the full annihilator subgroup functor. The theorem
`range_galoisTranslate_eq_of_annihilator` states the corresponding
equality of full ranges for any supplied representation of this
annihilator, using the base-changed inclusion followed by the canonical
ambient recovery isomorphism. Representability is an explicit supplied
equality; it is not claimed for an arbitrary submodule.

Every statement concerns all test schemes, retaining nonsmooth and
infinitesimal subgroup structure in every characteristic. No
finite-degree or Galois-extension assumption is made. Application to the
type-D vector cover still needs its construction, the exact integral
character-image calculation, and the comparison of its full group kernel
with the corresponding torus kernel.
