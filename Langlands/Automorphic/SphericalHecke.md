# Standard spherical Hecke operators on actual automorphic forms

This module internally specializes the existing local action on actual adelic
functions to the canonical spherical Hecke algebra. It applies to a number
field `K : Type u`, an actual finite place `v`, and positive matrix rank
`n = r + 1`. Coefficients are complex. All form spaces are the existing spaces
from `Langlands.Automorphic`; there is no new representation carrier.

## Construction and normalization

`automorphicLocalRightAction_isSmooth_canonical` transports the proved
smoothness of local right translation along
`FiniteAdelicGL.localGL_topology_eq`. The finite completion is the underlying
field of `CompletionPadic.padicField v`, but the canonical general-linear
topology and its Borel measurable space are supplied explicitly. The local
Haar instance is the existing `Unramified.sphericalHaar_isHaar`.

`AutomorphicSphericalVectors K v r` is exactly the fixed submodule for
`Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r`, namely
the canonical integral matrix subgroup. `automorphicSphericalHeckeAction`
is the unital algebra homomorphism from the existing actual spherical corner
to endomorphisms of this fixed space, obtained from `Hecke.cornerAction`.
Its Haar measure gives that subgroup mass one.

`automorphicStandardHeckeOperator` applies this homomorphism to
`Unramified.standardHeckeElement`. For `i : Fin (r + 2)`, this is the
characteristic function of the double coset of the diagonal matrix with
`i` canonical uniformizers followed by ones. The zeroth operator is the
identity, proved by preservation of the corner unit.

`evaluate_automorphicStandardHeckeOperator` identifies its value at the
actual adelic point `x` with

`integral h_i(g) f(x * ofFinite(localInclusion(g))) d(sphericalHaar)(g)`.

The theorem follows from `Hecke.integratedAction_dual` and evaluation on
the existing form space. Translation uses `g`, without inversion. The
integral is the complex scalar integral; the existing integrated action
already constructs the algebraic operator on smooth vectors.

`mem_automorphicSphericalVectors_of_standardIntegral` proves that invariance
under the global finite-adelic standard integral subgroup implies spherical
invariance at this place. It combines the proved equality of the local
integral and canonical spherical subgroups with the existing local-insertion
fixed-vector lemma.

## Eigenforms

`IsSphericalHeckeEigenform` requires a nonzero spherical form and the existing
`Unramified.standardHeckeScalar` equations for all standard operators. The
multiset retains multiplicities; the normalization is the positive real
square root of the actual residue cardinality embedded into the complex
numbers, raised to `i*(n-i)`, times the signed Euler coefficient.

## Provenance and scope

This is an internal construction from the published `LocalAction`,
`LocalHecke`, `PadicComparison`, `HeckeOperators`, `CornerAction`, and
fixed-vector APIs. Its mathematical obligations are specialization,
topology transport, fixed-vector inclusion; their Lean
proofs are described above. The normalization and source-based local
Hecke definitions are reused unchanged from `HeckeOperators` and its
paired documentation. No additional external theorem is asserted here.

Restricting the full automorphic-form space to a local group does not make
it irreducible or admissible. This module neither constructs an irreducible
local component nor asserts eigenform existence, the normalized
principal-series/Hecke spectral comparison, a Satake classification, or
weak automorphic induction. The eigenform predicates are relations on
actual forms, without any chosen parameter or classification assumption.
