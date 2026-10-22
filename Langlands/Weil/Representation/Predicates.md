# Separate conditions on complex Weil representations

Worker 17 supplies predicates on the actual finite-dimensional complex vector
spaces of `Langlands.FiniteRepresentation`. The input is a group with an
explicit inertia subgroup where needed. The generic definitions do not claim
that an arbitrary input group is a local Weil group.

The declarations keep the following conditions separate:

| Declaration | Meaning |
| --- | --- |
| `IsIrreducible` | Mathlib's nontrivial representation with no proper nontrivial invariant subspace. |
| `IsSemisimple` | The lattice of invariant subspaces is complemented. |
| `inertiaKernel` | Kernel of the restricted representation on the subgroup `I`. |
| `HasFiniteInertiaImage` | The image of that restricted representation is a finite set. |
| `IsUnramified` | Every element of `I` acts as the identity. |
| `HasFiniteImage` | The image of the full group is a finite set. |
| `IsUnitary` | Some positive-definite Hermitian inner product is preserved by the action. |
| `IsContinuous` | The homomorphism into complex endomorphisms is continuous for their usual finite-dimensional topology. |
| `HasOpenInertiaKernel` | The restricted kernel is open in `I` with the subgroup topology. |
| `IsGaloisTypeAlong j` | There exists a continuous representation of the target of `j` on the same carrier, whose pullback is the given action. |

The name `IsUnitary` means unitarizability of an abstract vector-space
representation; it does not select an inner product. `InnerProductSpace.Core`
includes positivity, definiteness, sesquilinearity and Hermitian symmetry.
`IsContinuous` uses `moduleTopology ℂ (Module.End ℂ A)`. This is Mathlib's
canonical module topology with the usual topology on the complex numbers.
On finite-dimensional complex vector spaces it agrees with the usual
Hausdorff vector-space topology; see Mathlib's
`isModuleTopologyOfFiniteDimensional`. In particular, this definition does
not put the discrete topology on the coefficients. Continuity in the group
variable is explicitly required; merely having continuous linear operators
would not state that requirement.

`ContinuousObjects` and `OpenInertiaObjects` are separate subtypes of all
finite-dimensional representations. `ContinuousIrreducibleClasses` and
`OpenInertiaSemisimpleClasses` use the genuine linear-isomorphism quotients
from `Basic`, and then restrict the descended rank to `n`. No equivalence
between continuity, open inertia kernel, or finite inertia image is used.
Similarly, finite image is not defined to mean Galois type. Such bridges
require hypotheses on the actual Weil and Galois groups and remain separate
theorem obligations. No topological-group instance is needed merely to state
these predicates.

## Source correspondence and scope

Tate, *Number theoretic background* (1979), section 2, printed pages 9–10
(PDF pages 18–19 of `Part II.pdf`), uses continuous complex representations
on vector spaces and discusses finite inertia and Galois type. Section 4.1.2,
printed page 20 (PDF page 29), uses the open-inertia-kernel algebraic
convention for Weil–Deligne data. The present declarations expose both
conventions without importing the comparison arguments.

- Literature ID: `tate-1979-number-theoretic-background`.
- Source SHA-256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

Henniart, *Représentations du groupe de Weil d'un corps local* (1980),
section 2.1 and the opening of section 2.2, printed page 158 (PDF page 5),
defines Galois type by extension along the map from the Weil group to the
absolute Galois group, and unramifiedness by triviality on inertia. Although
that source also states the finite-image equivalence, this module does not
assume or prove it.

- Literature ID: `henniart-1980-weil-representations`.
- Source SHA-256: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
un corps p-adique* (2000), section 1.1, printed page 439 (PDF page 1), uses
the continuous irreducible rank-`n` isomorphism classes. The rank-indexed
continuous irreducible set here is its generic group-level interface.

- Literature ID: `henniart-2000-simple-proof`.
- Source SHA-256: `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

Irreducibility and semisimplicity reuse the pinned Mathlib definitions.
The unitary predicate is the standard invariant positive-definite Hermitian
form definition, expressed directly using Mathlib's inner-product core;
no theorem about existence of such a form is assumed.
Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
This pair and its `Basic` dependency are development pending independent review.
