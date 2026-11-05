# Derived unramified spectra of actual tensor presentations

This internal construction inhabits the published
`FiniteTensorPresentation.UnramifiedData` from a genuine nonzero tensor
presentation and irreducibility and admissibility of its original factors
outside a finite exceptional set. The eigenvalue multisets and whole-space
Hecke scalar equations are derived from the published local existence theorem.
They are no longer additional inputs to this constructor.

## Inputs and conventions

Fix a number field `F : Type uF`, positive matrix rank `n = r + 1`, and
complex factor spaces `V v : Type uV` at its finite places. The universes
`uF` and `uV` are independent. The representations `ρ v` act on the actual
completed-local general linear groups. The tensor inputs include a finite set
`E` and reference vectors `e v` fixed by the actual integral subgroup outside
`E`. A supplied `FiniteTensorPresentation P` contains nonzero reference
vectors outside `E` and a genuine equivariant linear equivalence from the
restricted tensor space onto an actual finite-adelic-invariant form subspace
`S`. There is no finite-dimensionality requirement on `S`.

The constructor also requires `hS : S ≠ ⊥`, a finite set `T` containing
`E`, and irreducibility and admissibility of each original factor `ρ v`
for `v ∉ T`. Admissibility uses the published completed-local topology and
includes smoothness and finite generation of the fixed submodule for every
open subgroup. Neither the presentation nor these local properties are
asserted to exist for arbitrary automorphic subspaces.

All spherical operators are the original `LocalRealization.standardHeckeOperator`
on the original actual embedded component. The canonical p-adic object has
this same carrier and representation. The existing topology comparison and
integral-subgroup comparison supply the canonical p-adic interpretation.
The Haar measure gives the spherical subgroup mass one. For
`i : Fin (r + 2)`, the scalar is exactly

`sqrt(q)^(i*(n-i)) * (-1)^i * coeff_i(∏(1-αX))`,

with the positive real square root embedded into the complex numbers. The
spectrum is an unordered multiset of exactly `n` complex units; it retains
all multiplicities. Every standard index, including zero and the last index,
and every vector of the spherical fixed submodule occur in its scalar laws.

## Local existence and uniqueness

`LocalRealization.exists_sphericalHeckeSpectrum` applies the published
`Unramified.sphericalHeckeSpectrumExistence` to the actual local realization's
`padicObject`. It requires irreducibility, admissibility, and a nonzero
spherical fixed submodule. The object's fixed space, operators and spectral
relation are definitionally those of the original local realization, so this
specialization changes no eigen-equations or carriers. It constructs the
whole-space spectral relation rather than only one eigenvector.

`LocalRealization.eq_of_hasSphericalHeckeSpectrum` specializes the published
`Unramified.eq_of_hasSphericalHeckeSpectrum` to that same object. Two spectra
satisfying its original operator equations are equal as multisets with
multiplicities. `existsUnique_sphericalHeckeSpectrum` combines the existence
and separation results. These lemmas concern the Hecke spectral relation;
there is no principal-series realization conclusion.

## Actual presentation constructor

`localComponent_sphericalVectors_ne_bot` obtains a nonzero vector of the
actual `P.localComponent hS v` fixed by the actual integral subgroup from
`localComponent_exists_integral_fixed`. The published equality
`localIntegral_eq_sphericalSubgroup` makes this a nonzero member of the
spherical fixed submodule. This argument uses neither irreducibility nor
admissibility.

`P.unramifiedData hS T hET hI hA` constructs every field of
`P.UnramifiedData hS T`. Outside `T`, the inclusion `E ⊆ T` gives
`v ∉ E`. The previous nonzero-fixed-space result supplies sphericality.
The genuine `localComponentEquiv` transports the supplied original-factor
irreducibility and admissibility to the actual embedded component via the
published two equivalences. The local existence lemma then provides a
spectrum with the original whole-space scalar equations. Classical choice
selects this spectrum at each place; its proved property supplies
`hasSpectrum`. The other fields retain exactly `hET`, `hI`, and `hA`.

The resulting object can directly use every published `UnramifiedData`
operation: its actual p-adic class relation, ambient eigenform existence,
power traces, Euler polynomial and realizing invertible-matrix existence,
and its exported `spectralSystem`. In particular, these operations now have
a constructed input without any supplied spectral witness. Their existing
normalizations and limitations are unchanged.

## Uniqueness and compatibility

`UnramifiedData.eigenvalues_eq` applies local separation to any two data
objects for the same `P`, `hS`, and `T`. The original factor properties
stored in the first object provide the required local object. Function
extensionality makes their eigenvalue functions equal. All remaining
structure fields are proofs, so proof irrelevance yields `unique` and a
`Subsingleton` instance. This is uniqueness even for independently supplied
data, rather than a property of one particular choice operation.

`unramifiedData_eq` identifies the constructed object with every supplied
object for that same presentation and exceptional set. The restriction
operation and the fresh construction after enlarging `T` therefore agree
as data objects (`unramifiedData_restrict`). Likewise, transporting to any
other nonzero presentation of the same full tensor data agrees with fresh
construction there (`unramifiedData_transport`). Combining this equality
with the published invariance of the exported system under transport gives
`unramifiedData_spectralSystem_eq`. These comparisons preserve the full
family `V, ρ, E, e, he`; they do not compare unrelated tensor families.

## Provenance and remaining obligations

This module makes no new identification with original literature. It is an
internal specialization and assembly of published constructions and proofs:
`PresentedSpectralSystem`, `LocalSphericalHecke`, `PadicLocalCategory`,
`PresentedLocalComponent`, `SphericalHeckeSpectrumExistenceProof`, and
`SphericalSpectrumUniquenessProof`. Local existence and scalar separation
are reused by Lean name. The intrinsic construction proofs use the actual
fixed reference vector, property transport along the genuine local
equivalence, classical choice with its proved specification, function
extensionality, and proof irrelevance.

The module constructs unramified Hecke data under the stated genuine input
conditions. It does not construct an automorphic presentation, prove its
factors irreducible or admissible, classify spherical representations,
construct an isobaric automorphic realization, or supply arithmetic
Frobenius data or weak global association. These remain separate obligations.
