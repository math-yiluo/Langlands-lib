# Geometric Frobenius lifts at number-field completions

Author: Worker 41.
Closure-comparison documentation clarification: Worker 100.

This module constructs a geometric Frobenius lift at every actual finite place
of a number field, then defines evaluation of a genuine Galois representation's
Euler polynomial at that lift. The lift satisfies the already published
`Langlands.GaloisRepresentation.IsGeometricFrobeniusLift` predicate. All
construction obligations are proved, using published residue comparison,
residue-action surjectivity and finite-field Frobenius.

## Objects and construction

Let `K : Type uK` be a number field and `v : Global.FinitePlace K`. The local
group is `Field.absoluteGaloisGroup (Global.FiniteCompletion K v)`.
The residue extension is exactly `LocalResidueClosure v`, the residue field
of the spectral valuation on the algebraic closure of that completion, over
the residue field of `LocalGalois.baseIntegers` of the same completion.
The `Valued` scope supplies the canonical adic norm, as in `CompatibleFamily`
and `CompletionResidue`. No change of norm, algebraic closure or residue action
is made.

`residueArithmeticFrobenius` applies the published
`Galois.FiniteField.arithmetic` to this algebraic residue extension.
Finiteness of the base residue field comes from `CompletionResidue`;
algebraicity of the extension follows from the integral residue-extension
instance in `SpectralProof`. The intrinsic formula
`residueArithmeticFrobenius_apply` identifies its action with
`x ↦ x ^ residueCardinality v`. It unfolds finite-field Frobenius and rewrites
the chosen `Fintype` cardinality as `Nat.card`, then uses
`CompletionResidue.card_residueField` to obtain the absolute ideal norm.

`localResidueAction_surjective` specializes
`LocalGalois.residueHom_surjective` to the actual completion and its algebraic
closure. The proof supplies characteristic zero of the completion by its
injective algebra map from the number field; Mathlib then supplies the Galois
instance for its algebraic closure. Completeness, the ultrametric norm and
finite residue field come from the existing instances. Surjectivity has no
new assumption.

`exists_geometricFrobeniusLift` lifts arithmetic Frobenius through that
surjective residue action, and inverts the resulting Galois element. The
inverse of this chosen inverse acts as the cardinality power, exactly the
condition in `IsGeometricFrobeniusLift`. `geometricFrobeniusLift` makes a
classical choice from the proved existence, and `geometricFrobeniusLift_spec`
records its property. This is an arbitrary lift, not a canonical Galois
element or a group-homomorphic section of the residue action.

## Euler evaluation and matching

For a genuine continuous finite-dimensional representation
`A : Objects K L`, with coefficient field `L : Type uL`, its specified
topology and carrier universe `uV`, `frobeniusEulerPolynomial A v` is
`eulerPolynomial (atFinitePlace v A) (geometricFrobeniusLift v)`.
Thus it retains the existing geometric convention `det(1 - rho(Frob_v) T)`.
It is defined even for ramified representations, but no independence of the
geometric lift or local-factor interpretation is asserted in that case.

For `IsUnramifiedAt A v`, `frobeniusEulerPolynomial_eq_of_lift` identifies
this value with evaluation at any geometric lift, by the published kernel
argument in `CompatibleFamily`. The intrinsic consequences are:

- `hasEulerPolynomialAt_iff`: existing existential matching is equivalent
  to unramifiedness and equality with the constructed polynomial.
- `IsUnramifiedAt.hasEulerPolynomialAt`: every unramified representation
  matches its constructed polynomial.
- `HasEulerPolynomialAt.unique`: two matching polynomials are equal.
- `isUnramifiedAt_iff_existsUnique_eulerPolynomial`: unramifiedness is
  equivalent to existence of a unique polynomial satisfying the existing
  matching predicate. Existence uses the constructed lift; uniqueness uses
  lift independence.
- `matchesOutside_iff`: the existing family condition is equivalent to
  unramifiedness and equality of the constructed polynomial with the image of
  the common coefficient-field polynomial at each retained coefficient
  place. It preserves the finite coefficient exclusions, base exceptional
  set and inequality of residue characteristics exactly.

The base-field, coefficient-field and representation-carrier universes are
independent. For the family lemma the coefficient field is a number field,
and each representation uses its actual completion topology, as in
`Collection` and `MatchesOutside`.

## Provenance and exact sources

This is a derived construction, not a new formulation of an automorphic
existence theorem. Its algebraic inputs are the four published modules
listed below, and its intrinsic proofs implement the route just described.

The geometric convention agrees with John Tate, *Number theoretic
background*, in Corvallis Part II (1979), Section 1.4.1, printed p.6
(retained `Part II.pdf`, PDF p.15). Inertia fixes the residue closure,
arithmetic Frobenius acts by the residue-cardinality power, and Tate uses
the inverse for the uniformizer convention. This page was read directly
in the registered original `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The lift existence proof here is derived from the published surjectivity
theorem, rather than imported as an assumption from the source.

The Euler convention and family-matching interpretation agree with Michael
Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Inventiones mathematicae 134 (1998), Section 1, printed p.183 (PDF p.7).
Harris uses geometric Frobenius, the determinant `det(1 - rho(Frob_v) T)`,
one finite base exceptional set, finite coefficient-place exclusions, and
the exclusion of the coefficient residue characteristic. This page was read
directly in `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
Both original-file fingerprints were recomputed. No errata files for these
sources were present in the current Library or project notes.

## Dependency map and boundaries

All project imports are published modules, read at Library commit
`a175d25f6a5a9e22525012e3cae66e9f8dfacba9`:

| Module | Reused declarations |
| --- | --- |
| `Langlands.Galois.CompatibleFamily` | Actual local group and residue extension; residue action and inertia; geometric-lift predicate; unramifiedness, matching and family predicates; Euler-polynomial independence |
| `Langlands.Galois.FiniteField.Frobenius` | `Galois.FiniteField.arithmetic` on any algebraic extension of a finite field |
| `Langlands.Galois.Local.SpectralProof` | `residueExtension_isIntegral`, `residueHom_surjective` |
| `Langlands.Global.CompletionResidue` | `finite_residueField`, `card_residueField` for the same canonical completion norm |

The finite-field implementation uses Mathlib's
`FiniteField.frobeniusAlgEquivOfAlgebraic`; its cardinality-power formula
and algebraic-extension hypotheses were inspected in
`Mathlib/FieldTheory/Finite/Basic.lean`. The pinned environment is Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

This module closes the lift-existence gap for the already published
compatible-family interface. Independence from a different compatible
global-to-local closure embedding is proved in the separately published
[`Langlands.Galois.ClosureRestriction`](ClosureRestriction.md). Using that
comparison requires importing `Langlands.Galois.ClosureRestriction`; it is
not supplied by importing `FrobeniusLift` or `CompatibleFamily` alone.

For `ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)`,
`Langlands.GaloisRepresentation.atFinitePlaceAlongClosureEquiv v ι A`
constructs an actual representation equivalence from
`atFinitePlaceAlongClosure v ι A` to `atFinitePlace v A`.
`eulerPolynomial_atFinitePlaceAlongClosure_eq` proves equality of their
Euler polynomials at every same `g : LocalGroup v`, without an
unramifiedness hypothesis.
`isUnramifiedAt_iff_alongClosure` identifies `IsUnramifiedAt A v` with
triviality of the specified-embedding restriction on the fixed actual
`localInertia v`. `hasEulerPolynomialAt_iff_alongClosure` identifies
`HasEulerPolynomialAt A v P` with that same inertia-triviality condition
conjoined with the existence of an actual `g : LocalGroup v` satisfying
`IsGeometricFrobeniusLift v g` and having Euler polynomial `P` for the
specified-embedding restriction. These names have prefix
`Langlands.GaloisRepresentation`.

Closure-embedding independence keeps the algebraic closure of the completion,
the actual local group and the residue-action model fixed. It asserts neither
equality nor canonicity of the raw restriction homomorphisms. It is distinct
from independence of different geometric Frobenius elements, proved under
unramifiedness in `CompatibleFamily` by
`Langlands.GaloisRepresentation.eulerPolynomial_eq_of_geometricFrobenius`, and from
lift existence, proved here by `exists_geometricFrobeniusLift`. The chosen
geometric lift remains arbitrary. Changing the residue-closure model or
transporting to a separately constructed local-field realization is outside
these results.

The closure comparison is a derived representation consequence of the
construction documented in `ClosureRestriction`, motivated by Serre,
*Local Fields*, Chapter X, Section 4, printed pp.155–156 (PDF pp.161–162).
Serre's Proposition 5 concerns induced cohomology maps; these representation
results are not an assertion of that proposition. The registered original is
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

No compatible family is constructed from automorphic forms or Shimura
cohomology here; purity,
multiplicity removal, semisimplicity, geometric origin and Hodge–Tate
properties are not consequences of this module. It does not define a
ramified Euler factor via inertia invariants or establish ramified local
compatibility. The full host theorem-statement task remains incomplete.

Original development compilation and declaration inspection succeeded without errors
or warnings. Complete types preserve independent universes and introduce no
extra Galois, finite-residue-field or lift-existence assumption. Unapplied
assignments checked the full existence and unique-matching theorem types.
The inspected construction and matching proofs use only `propext`,
`Classical.choice` and `Quot.sound`. This is development evidence; independent
semantic review and publication remain separate.
