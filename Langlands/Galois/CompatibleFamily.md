# Compatibility of actual lambda-adic Galois representations

Author: Worker 41.
Documentation correction (I028): Worker 32.
Closure-comparison documentation clarification: Worker 100.
It defines compatibility and purity, and proves the independence of
geometric-Frobenius lifts needed by the definition. The published companion
`Langlands.Galois.FrobeniusLift` proves lift existence for these same local
objects. Neither module proves an existence theorem for automorphic Galois
representations.

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
The predicate itself does not choose a lift; existence is proved separately by
`Langlands.GaloisRepresentation.exists_geometricFrobeniusLift` in the companion.
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
gives the same equality for every geometric lift. The existential clause
records an actual witness; the companion now supplies one for every `v`.
Its theorem `Langlands.GaloisRepresentation.hasEulerPolynomialAt_iff` states

`HasEulerPolynomialAt A v P ↔
  IsUnramifiedAt A v ∧ frobeniusEulerPolynomial A v = P`.

Here `frobeniusEulerPolynomial A v` evaluates the existing Euler polynomial
at `geometricFrobeniusLift v`, chosen from the proved existence theorem.
All these names have prefix `Langlands.GaloisRepresentation`. Evaluation is
defined even for ramified representations, but equality with evaluation at
every geometric lift requires `IsUnramifiedAt A v`. The equivalence retains
that condition; it does not infer unramifiedness from a chosen-lift identity.
The chosen lift is not asserted to be canonical.

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

The original dependency record below concerns Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`: the published dependencies were
`Langlands.Global.Adelic`,
`Langlands.Weil.Representation.Basic`,
`Langlands.Galois.Local.SpectralDefinitions` and
`Langlands.Cohomology.Weights.Polynomial`. The then-new paired
`Langlands.Galois.CoefficientRepresentation` supplies the actual continuous
representation and restriction layer.

For every number field `K` and actual finite place `v : Global.FinitePlace K`,
the published `Langlands.GaloisRepresentation.exists_geometricFrobeniusLift`
proves `∃ g : LocalGroup v, IsGeometricFrobeniusLift v g`. It uses exactly
this module's `LocalGroup`, `localResidueAction`, `LocalResidueClosure` and
`residueCardinality`, with the same canonical completion norm. The companion
imports this module, so using its existence and chosen-lift theorems requires
importing `Langlands.Galois.FrobeniusLift`.

The residue comparison is also proved.
`Langlands.Global.CompletionResidue.residueEquiv` identifies
`NumberField.RingOfIntegers K ⧸ v.asIdeal` with
`IsLocalRing.ResidueField
  (Langlands.LocalGalois.baseIntegers (Global.FiniteCompletion K v))`
through the actual embedding and reduction map.
`Langlands.Global.CompletionResidue.card_residueField` identifies its
`Nat.card` with `Ideal.absNorm v.asIdeal`, exactly `residueCardinality v`.
The companion's `Langlands.GaloisRepresentation.residueArithmeticFrobenius_apply`
therefore gives the cardinality-power action on `LocalResidueClosure v`.
Its `Langlands.GaloisRepresentation.localResidueAction_surjective` specializes
the proved spectral residue-action surjectivity to this completion. Lifting
arithmetic Frobenius and taking the inverse proves the geometric-lift
existence assertion without an additional existence hypothesis.

These intrinsic results were checked in Library commit
`5150bf6c9c8e6dd90b1329f6188324b9fb00a0da`, and the Tate and Harris passages
above were reread for the I028 correction. They use the number-field completion
directly. Independence under a different compatible global-to-local closure
embedding is a separate arithmetic comparison already proved in the published
[`Langlands.Galois.ClosureRestriction`](ClosureRestriction.md). It requires
importing `Langlands.Galois.ClosureRestriction`; importing `CompatibleFamily`
or `FrobeniusLift` alone does not supply it.

For `ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)`,
`Langlands.GaloisRepresentation.atFinitePlaceAlongClosureEquiv v ι A`
constructs an actual representation equivalence from
`atFinitePlaceAlongClosure v ι A` to the existing `atFinitePlace v A`.
`eulerPolynomial_atFinitePlaceAlongClosure_eq` gives equality of their
Euler polynomials at every same `g : LocalGroup v`, without assuming
unramifiedness. `isUnramifiedAt_iff_alongClosure` identifies the existing
unramifiedness predicate with triviality of the specified-embedding
restriction on the fixed actual inertia subgroup `localInertia v`.
`hasEulerPolynomialAt_iff_alongClosure` identifies `HasEulerPolynomialAt A v P`
with the conjunction of that inertia-triviality condition and
`∃ g : LocalGroup v, IsGeometricFrobeniusLift v g ∧
  eulerPolynomial (atFinitePlaceAlongClosure v ι A) g = P`.
All these declarations have prefix `Langlands.GaloisRepresentation`.
The existential actual lift is retained.

This closure-embedding independence fixes the algebraic closure of the
completion, the actual local group and the residue-action model. Raw
restriction homomorphisms are not asserted equal or canonical. The
same-element comparison does not assume unramifiedness, whereas independence
of different geometric Frobenius elements is the distinct theorem
`eulerPolynomial_eq_of_geometricFrobenius` in this module, which requires it.
Lift existence is the separate `exists_geometricFrobeniusLift` theorem in
`FrobeniusLift`; its chosen geometric lift remains arbitrary. The closure
comparison is derived from the construction documented in `ClosureRestriction`,
whose source motivation is Serre, Chapter X, Section 4, printed pp.155–156
(PDF pp.161–162). Serre's Proposition 5 concerns induced cohomology maps;
the representation consequences are derived results of the companion.

Changes of residue-closure model and transport to a separately constructed
local-field realization, including a finite extension of `Q_p`, remain
outside these results. Local Weil-group assembly belongs to the
separate `Langlands.Weil.Local.Assembly` and `AssemblyProof` modules; it is
not a consequence of this lift-existence theorem. Full compatible-family or
automorphic Galois-representation existence, purity of cohomology,
multiplicity removal, automorphic weak association with its unitary
normalization, and ramified compatibility are not supplied by these
intrinsic lift and Euler-polynomial results.

The original development used Lean 4.34.0 and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Native compilation and the exact
Lake check succeeded with zero errors or warnings. The latter reports
`IsCompatible` as a definition returning `Prop`, with independent universes
for the base, coefficient and representation carrier. This development
evidence does not establish independent semantic acceptance or publication.

## Declaration and dependency map

All names defined in this module below have prefix `Langlands.GaloisRepresentation`.

| Declarations | Meaning and dependency |
| --- | --- |
| `residueCharacteristic`, `residueCardinality` | Quotient-ring characteristic and absolute ideal norm of the published actual finite place |
| `LocalGroup`, `LocalResidueClosure`, `localResidueAction`, `localInertia` | Actual completion's algebraic-closure automorphisms, spectral residue field, published reduction action and its kernel |
| `IsGeometricFrobeniusLift` | Inverse-residue-action power formula with the actual absolute norm |
| `IsUnramifiedAt` | Triviality of the actual restricted action on the kernel |
| `HasEulerPolynomialAt` | Unramifiedness, existence of a geometric lift, and equality of its Euler polynomial |
| `residueAction_eq_of_geometricFrobenius`, `action_eq_of_residueAction_eq`, `eulerPolynomial_eq_of_geometricFrobenius`, `HasEulerPolynomialAt.forall_lifts` | Proved independence of lift using the actual kernel and representation laws |
| `Collection`, `MatchesOutside`, `IsCompatible`, `HasRank`, `IsPureCompatible` | Actual coefficient-indexed collection and separate compatibility, dimension and integral-weight propositions |

The following fingerprints record dependencies of the original submission at
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`:

| Published module | SHA256 |
| --- | --- |
| `Langlands.Global.Adelic` | `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e` |
| `Langlands.Weil.Representation.Basic` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Galois.Local.SpectralDefinitions` | `7b05ea4f6904f852d6870c3c323a42939d98c8e03bfc08fb7aa37a58d46e8d9a` |
| `Langlands.Cohomology.Weights.Polynomial` | `47a03391e9b60f456f2b30133179940bb3fa75ee2b8c740b03641aaa0742964f` |

Their paired Markdown was read and the original workspace copies were checked
against the published bytes. `CoefficientRepresentation` was the sole new
helper pair included with that submission. No unreviewed global automorphic,
cohomological or local-Weil draft is imported. The I028 correction changes
only this Markdown; the Lean module and its imports are unchanged.
