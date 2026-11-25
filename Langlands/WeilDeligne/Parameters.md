# Complex Weil–Deligne parameters and their rank-indexed classes

This module adds the topological conditions to the algebraic pair category
of `WeilDeligne.Basic`. The group, inertia subgroup, norm character and
integer degree map are supplied explicitly. The local-field module
`Langlands.Weil.Local.Parameters` instantiates them from the actual Weil
pullback of `Langlands.Weil.Local.Assembly`.

`IsParameter I A` means that the underlying complex representation has
open inertia kernel, exactly through the separately defined
`FiniteRepresentation.HasOpenInertiaKernel`. `IsContinuous` instead asks
for usual-topology continuity. No comparison theorem between these
conditions is assumed.

`ParameterObjects` is a subtype of actual pairs satisfying the inertia
condition. `parameterSetoid` restricts the genuine pair-isomorphism
relation to this subtype, so its quotient `ParameterClasses` still uses
actual invertible linear maps commuting with both the group action and
monodromy. `parameterClassForget` descends the underlying-pair map to
unrestricted classes. `ParameterClassesOfRank` uses its well-defined rank.

The analogous `FrobeniusSemisimpleParameterClasses` adds the explicit
predicate that each nonzero-degree action operator is semisimple. Its
rank-indexed version is
`FrobeniusSemisimpleParameterClassesOfRank`. Neither the subtype nor its
quotient contains a requirement that monodromy vanish. The generic
degree map is not assumed to be surjective; actual geometric Frobenius
existence is an independent local Weil obligation.

`zeroMonodromyParameter` sends a representation with a supplied proof of
open inertia kernel to the actual zero-monodromy pair. Its parameter
condition follows from the unchanged underlying representation. It makes
no claim that an arbitrary such representation is Frobenius semisimple.

## Provenance

Tate, *Number theoretic background* (1979), section 4.1.2–4.1.7,
printed pages 20–21 (PDF pages 29–30 of `Part II.pdf`), supplies the
open-inertia convention, the separate Frobenius-semisimplicity condition,
and the rank-indexed isomorphism classes of Weil–Deligne representations.
The explicit subtype, quotient and forgetful-map constructions implement
those conditions using the proved genuine isomorphism relation from
`Basic`; they assume no classification, semisimplification constructor,
or continuity equivalence.

- Literature ID: `tate-1979-number-theoretic-background`.
- Source SHA-256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
- `WeilDeligne.Basic` is ported together with this module.
- The external project definition dependency is the
  finite-representation foundation under `Langlands.Weil.Representation`,
  published at Library commit
  `843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Its `Basic` and `Predicates` pairs
  retain their exact source hashes.

This pair compiles in the pinned environment.

Additional source alignment: Henniart, *Une caracterisation de la
correspondance de Langlands locale pour GL(n)* (2002), §1.1, printed
page 588, uses complex finite-dimensional Frobenius-semisimple parameters
for his set G(n). This corresponds to the separate
`FrobeniusSemisimpleParameterClassesOfRank`, not to the unrestricted
pair type or general `ParameterClassesOfRank`. The equivalence between
Frobenius semisimplicity and other formulations is not assumed here.
Source ID `henniart-2002-characterization`, retained PDF SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
