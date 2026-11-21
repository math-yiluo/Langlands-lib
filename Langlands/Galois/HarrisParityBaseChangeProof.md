# Automorphic base change in the Harris parity argument

`Langlands.GaloisRepresentation.harrisParityBaseChange` proves
`HarrisParityBaseChangeStatement`. Given the four premises in the statement,
it constructs a cuspidal realization `T` over the quadratic CM extension `N/E`
whose class is the weak base change of the given realization `S`. The same
`T` is regular algebraic and conjugate self-dual, and has a square-integrable
component at each place above the distinguished split place.
[Statement and scope](HarrisParityBaseChangeStatement.md)

## Constructing the lift

The unitary central character of `S` makes its singleton isobaric datum
unitary. Since `N/E` is quadratic and Galois, its automorphism group is cyclic
of order two. The prime-degree isobaric premise gives a unitary weak transfer
of the singleton and uniqueness among unitary weak transfers. The split
comparison applies to the spectral presentation witnessing the
square-integrable component of `S`. It identifies the upper datum with the
singleton of an actual `T` and supplies a spectral presentation of `T`
witnessing square-integrability at every place above the split place. The
singleton comparison gives the cuspidal weak base-change relation.

## Regular algebraicity

The complex-parameter bridge supplies lower place parameters and an
infinitesimal character acting by scalars. Evaluating on a nonzero vector
identifies that character with the given regular algebraic infinitesimal
character. The bridge then gives the Clozel regular algebraicity conditions on
each lower parameter list. At every upper complex place the weak-transfer
comparison carries the list from its restriction to `E`. The labelled
transport retains the list or conjugates its blocks, which exchanges
the two exponent lists. Length, integrality, and the absence of repetitions
in both exponent lists are preserved. Applying the bridge to all the upper
lists gives the regular algebraic infinitesimal character of `T`.

## Conjugate self-duality

The proof chooses actual cuspidal contragredients of `S` and `T`. At cofinally
many finite places the corresponding dual spectral presentations invert each
unramified eigenvalue. Inversion commutes with raising to the residue degree,
so the duals retain the weak base-change relation.

Next, arithmetic pullback of both spectral presentations by the CM
involutions realizes their CM conjugates. The involutions commute with the
field inclusion and send places above a given place to places above its
conjugate. The resulting residue-field isomorphisms commute with the algebra
maps, preserving residue degrees. The induced multiplicative equivalence on
ideals preserves the multiplicities computing the ramification indices. The
place equivalence pulls back the cofinite set of good comparisons. The
transported eigenvalues satisfy the weak base-change identities there with
the same residue-degree powers.

Pulling back the pairing in its second variable via the CM intertwiner
identifies conjugate self-duality with the ordinary contragredient pairing
for the CM pullback. The comparison checks the finite, compact and Lie
actions and preserves the realization of all smooth contragredient
functionals. Contragredient uniqueness therefore identifies the CM
conjugate of the lower dual with `S` up to equivalence. The CM conjugate of the
upper dual is unitary, so its singleton is another unitary weak lift of the
lower singleton. Isobaric uniqueness identifies it with the singleton of
`T`. Applying the CM involution gives the contragredient relation for the
CM pullback of `T`, and the pairing comparison gives the required conjugate
self-duality.

## Source

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties*, Annals of Mathematics Studies 151, Princeton University Press,
2001, proof of VII.1.9, printed p. 229 (PDF p. 237), use the split
square-integrable component, strong multiplicity one and the algebraic
infinitesimal character of the automorphic restriction. The formal proof
implements this step with the four stated premises and the Library's
realizations and spectral presentations. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura` (SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`).
