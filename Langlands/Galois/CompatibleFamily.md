# Compatibility of actual lambda-adic Galois representations

Author: Worker 41.
It defines compatibility and purity, and proves the independence of
geometric-Frobenius lifts needed by the definition. It proves no existence
theorem for automorphic Galois representations.

Let `K` and `L` be actual number fields. Finite places are the published
`Global.FinitePlace` objects, nonzero prime ideals in their rings of integers.
Their residue characteristic is `ringChar` of the actual quotient ring, and
their residue cardinality is the ideal's absolute norm. At `v` the local
Galois group is the actual absolute Galois group of `Global.FiniteCompletion K v`.

`localResidueAction` and `localInertia` reuse the Library's constructed spectral
valuation, residue action and its kernel on the algebraic closure of this
completion. No arbitrary group, residue homomorphism or inertia subgroup is
supplied as replacement data. `IsGeometricFrobeniusLift v g` says that the
inverse of this actual local Galois element acts on every residue element by
`x ↦ x^(Nv)`. Thus it fixes the geometric, rather than arithmetic, direction.
This condition does not choose or assert the existence of a lift.
The scoped Mathlib `Valued` instance supplies the nontrivial norm on the
actual number-field completion; no additional norm or valuation is an input.

The global representation is restricted to the completion through
`Langlands.GaloisRepresentation.atFinitePlace`, with its explicitly documented
choice of compatible algebraic closures. `IsUnramifiedAt` requires this
restriction to act trivially on the actual inertia kernel. The intrinsic proof
shows that equal residue actions have equal representation actions:
`g h⁻¹` is in that kernel, so its action is the identity. Two geometric lifts
have the same residue action by their defining power formula. Their
characteristic and Euler polynomials therefore agree.

`HasEulerPolynomialAt A v P` requires both unramifiedness and an actual
geometric lift whose Euler polynomial is `P`. The proved `forall_lifts` law
gives the same equality for every geometric lift. This existential clause
prevents a universal implication from making the condition vacuous if the
existence of lifts has not yet been proved in the local construction.

`Collection K L excluded` is a dependent collection of genuine continuous
finite-dimensional representations over the actual `L_lambda`, indexed by
the finite places outside the finite set `excluded`. It is not virtual
cohomology. Compatibility is the separate proposition `IsCompatible`:
there exist one finite set `S` of base places and polynomials `P_v` in `L[T]`
such that, for every retained coefficient place and every `v` outside `S`
whose residue characteristic is different, the representation has Euler
polynomial equal to the image of `P_v` in `L_lambda[T]`.

`HasRank` separately specifies a common dimension. `IsPureCompatible` requires
the same matching together with purity of the reversed common Euler
polynomials, using the published `IsPurePolynomial` definition and weight
`w`. It concerns a single fixed weight. Harris also allows sums of pure
collections of different weights; this pair does not identify that condition
with single-weight purity.

## Exact sources and remaining boundaries

The compatible-family convention and finite coefficient exclusions are from
Harris (1998), Section 1, printed pp.183–184, reread in the original.
`P_v(T)` means `det(1 - rho(Frob_v) T)`, so its reciprocal roots are the
eigenvalues. Registered original `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

The explicit inverse-power formula unfolds geometric Frobenius with the
convention in Tate (1979), *Number theoretic background*, Section 1.4.1,
printed p.6, retained `Part II.pdf` p.15. This passage was read in the original:
inertia fixes the residue closure, and a uniformizer corresponds to the
inverse of the cardinality-power automorphism. Registered original
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The residue-kernel construction is also described in Serre, *Local Fields*,
Chapter I, Section 7, printed pp.20–22, read in the retained original:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Its finite-extension surjectivity result is not assumed here.

The published imports are `Langlands.Global.Adelic`,
`Langlands.Weil.Representation.Basic`,
`Langlands.Galois.Local.SpectralDefinitions` and
`Langlands.Cohomology.Weights.Polynomial`, read at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. The new paired
`Langlands.Galois.CoefficientRepresentation` supplies the actual continuous
representation and restriction layer.

The local owner still must prove existence of geometric lifts, the residue
identification and cardinality comparison, and the relevant local Weil
assembly. No such existence theorem is embedded as an axiom or assumed
constructor argument. Here the number-field completion is used directly;
transport to a separately constructed finite extension of `Q_p` remains
another arithmetic comparison. Independence under a different choice of the
global-to-local closure embedding remains a separate theorem. Full compatible
family existence, purity of cohomology, multiplicity removal, automorphic
weak association with its unitary normalization, and ramified compatibility
are not consequences of these definitions alone.

All new code uses Lean 4.34.0 and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Native compilation and the exact
Lake check succeeded with zero errors or warnings. The latter reports
`IsCompatible` as a definition returning `Prop`, with independent universes
for the base, coefficient and representation carrier. This development
evidence does not establish independent semantic acceptance or publication.

## Declaration and dependency map

All new names below have prefix `Langlands.GaloisRepresentation`.

| Declarations | Meaning and dependency |
| --- | --- |
| `residueCharacteristic`, `residueCardinality` | Quotient-ring characteristic and absolute ideal norm of the published actual finite place |
| `LocalGroup`, `LocalResidueClosure`, `localResidueAction`, `localInertia` | Actual completion's algebraic-closure automorphisms, spectral residue field, published reduction action and its kernel |
| `IsGeometricFrobeniusLift` | Inverse-residue-action power formula with the actual absolute norm |
| `IsUnramifiedAt` | Triviality of the actual restricted action on the kernel |
| `HasEulerPolynomialAt` | Unramifiedness, existence of a geometric lift, and equality of its Euler polynomial |
| `residueAction_eq_of_geometricFrobenius`, `action_eq_of_residueAction_eq`, `eulerPolynomial_eq_of_geometricFrobenius`, `HasEulerPolynomialAt.forall_lifts` | Proved independence of lift using the actual kernel and representation laws |
| `Collection`, `MatchesOutside`, `IsCompatible`, `HasRank`, `IsPureCompatible` | Actual coefficient-indexed collection and separate compatibility, dimension and integral-weight propositions |

The dependency versions are the current Library commit specified above.
The Lean SHA256 fingerprints are:

| Published module | SHA256 |
| --- | --- |
| `Langlands.Global.Adelic` | `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e` |
| `Langlands.Weil.Representation.Basic` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Galois.Local.SpectralDefinitions` | `7b05ea4f6904f852d6870c3c323a42939d98c8e03bfc08fb7aa37a58d46e8d9a` |
| `Langlands.Cohomology.Weights.Polynomial` | `47a03391e9b60f456f2b30133179940bb3fa75ee2b8c740b03641aaa0742964f` |

Their paired Markdown was read and the workspace copies were checked against
the published bytes. `CoefficientRepresentation` is the sole new helper pair
included with this contribution. No unreviewed global automorphic,
cohomological or local-Weil draft is imported.
