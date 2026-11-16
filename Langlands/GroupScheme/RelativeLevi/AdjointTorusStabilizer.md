# The actual maximal-torus stabilizer inside the adjoint Borel

This is an internal construction by Worker 692 from the Library's relative
Levi self-normalization, maximal-torus center containment, Borel retraction,
actual right-coset projection, and represented-subgroup quotient construction.
It is a supporting step for the semilocal quasi-split inner-form problem.

Let `G` be reductive over `Spec R`, let `i : B ⟶ G` be a relative Borel, and
let `q : G ⟶ A` be a supplied fppf quotient with full kernel `center G`.
Suppose the supplied action of `A` on `G` restricts through `q` to conjugation.
Supply a commutative relative torus `T` and `t : T ⟶ B` whose ambient
composite is closed and fibrewise maximal. The existing actual Borel
stabilizer construction gives `qB : B ⟶ P` and `j : P ⟶ A`.

`IsRelativeBorelSubgroup.adjointTorusStabilizerData` constructs an actual
group scheme `D`, a closed monic inclusion `s : D ⟶ P`, and an fppf
projection `qT : T ⟶ D`. The full range of `s` is precisely the stabilizer
of the original ambient torus subgroup under the action restricted to `P`.
The equation `t ≫ qB = qT ≫ s` holds and its square is cartesian.
The retained quotient data give the full kernel equality
`range (kernelι qT) = (range (kernelι qB)).comap t`, hence the inverse
image of the original ambient center under `t ≫ i`.

The general-base lemma `maximalTorus_normalizer_comap` first identifies
the inverse image in `B` of the ambient torus normalizer with the torus.
A normalizing point normalizes the inverse-image subgroup, which is the
original torus because `i` is monic. Relative Levi self-normalization in
the Borel then gives the forward inclusion; functoriality of normalizers
gives the reverse inclusion.

For the construction, the commuting Borel quotient square and the action's
conjugation restriction identify the full inverse image of the desired
stabilizer under `qB` with `range t`. Stabilizer membership is fppf-local.
The full kernel of `qB` lies in `range t`, by maximal-torus containment
of the full center, including its non-smooth part.

The Borel retraction data retain an actual unipotent radical `U` and a
multiplication isomorphism `T × U ⟶ B`. Reversal supplies `U × T ⟶ B`,
whose inverse first coordinate is the actual scheme map `B ⟶ U` with
right-coset fibres for `T`. This map descends through `qB`. The radical
is affine over the base, since it is closed in the affine Borel, so it
is separated. The existing `quotientSubgroupDataOfCosetMap` therefore
represents the identity fibre as a closed subgroup of `P`; its exact
inverse image gives the cartesian square and the fppf projection.

No torus existence is assumed implicitly: the original torus and its
factorization are supplied. This construction does not yet assert that
the resulting group `D` is a torus, give an induced-torus presentation,
construct the Borel quotient's retraction to `D`, supply a radical
vector-bundle series, or prove the semilocal inner-form theorem.
