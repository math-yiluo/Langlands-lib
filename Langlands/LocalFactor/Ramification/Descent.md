# Maps and fixed spaces for a supplied finite inertia quotient

`Langlands.Ramification.Local` works with the finite inertia group of `L/K`
from `Langlands.LocalFactor.Ramification.Galois`. The supplied
`LocalField.TopologicalData K₀ L` gives the integer ring used in the inertia
construction. For a finite Galois subextension `L/K` of a separable closure,
this is the inertia group acting trivially on the residue field of `L`.
The descent takes a surjective homomorphism `π : J →* inertia T K` and a proof
that `π.ker` acts trivially in the representation of `J`.

`descendInertiaMap` retains the underlying linear map. Equivariance follows by
lifting each element of inertia along `π` and applying the original
intertwining identity. Identity and composition follow from equality of the
underlying maps. `descendInertiaEquiv` retains the underlying linear
equivalence. The kernel condition is invariant under equivalence, using
surjectivity of the linear equivalence and its inverse. The source and target
carriers may have independent universes, and these constructions work in any
vector space dimension.

`fixedVectors_descend_eq` identifies the fixed subspace for a subgroup `H`
of finite inertia with the fixed subspace of its inverse image `H.comap π`.
The equality follows by evaluating the descended action on lifts of elements
of `H`. At the whole inertia group it gives the original invariant subspace
of `J`. For a finite-dimensional representation this identifies the
codimensions and gives

`Artin(π, ρ) = (dim(V) − dim(V^J)) + Swan(π, ρ)`.

The codimension is a natural number cast to the rationals. Artin and Swan
use the published sums over the actual lower ramification groups. Equivalence
invariance is for representations descended along the same supplied `π`.
The quotient and the kernel condition are data throughout.

## Characteristic and specialization

The earlier p-adic form obtained finite inertia and the lower groups using
`F.TopologicalData` over `Padic p`. Here those constructions come from the
published general definitions in `Langlands.Ramification.Local`. In the
finite Galois application, separability belongs to the supplied extension.
The descent, fixed-space and conductor arguments use group actions and
linear algebra over the coefficient field and need no characteristic-zero
instance on either field. The conductor lemmas require `[FiniteDimensional K₀ L]`
for the terminating lower sums.

The p-adic declarations use `K₀ = Padic p`, `L = F.Carrier` and
`T.toLocalData`. Definitions unfold to the general constructions on these
inputs. Lemmas use the corresponding general proofs at the same inputs.

| `Langlands.Ramification.Local` | `Langlands.Ramification.Padic` |
| --- | --- |
| `descendInertiaMap` | `descendInertiaMap` |
| `descendInertiaMap_apply` | `descendInertiaMap_apply` |
| `descendInertiaMap_id` | `descendInertiaMap_id` |
| `descendInertiaMap_comp` | `descendInertiaMap_comp` |
| `kernel_le_of_equiv` | `kernel_le_of_equiv` |
| `kernel_le_iff_of_equiv` | `kernel_le_iff_of_equiv` |
| `descendInertiaEquiv` | `descendInertiaEquiv` |
| `fixedVectors_descend_eq` | `fixedVectors_descend_eq` |
| `fixedVectors_descend_top_eq` | `fixedVectors_descend_top_eq` |
| `fixedCodimension_descend_eq` | `fixedCodimension_descend_eq` |
| `artinConductorOfQuotient_eq_tame_add_swan` | `artinConductorOfQuotient_eq_tame_add_swan` |
| `artinConductorOfQuotient_equiv` | `artinConductorOfQuotient_equiv` |
| `swanConductorOfQuotient_equiv` | `swanConductorOfQuotient_equiv` |

## Provenance

The map, equivalence and fixed-space constructions are internal consequences
of the published `descendInertiaRepresentation` and its formula on elements
in the image of `π`. The conductor decomposition takes out the zeroth term
of the Artin sum. Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, GTM 67 (1979), Chapter VI, §2, Proposition 2 and Corollary 1′,
printed pp. 100–101 (retained PDF pp. 107–108), gives the classical conductor
sum weighted by `|Gᵢ| / |G₀|` with the codimension of each fixed space. The Lean
sums use rational values and permit arbitrary coefficient fields. Serre's
classical representation-theoretic interpretation is for complex coefficients.

Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
