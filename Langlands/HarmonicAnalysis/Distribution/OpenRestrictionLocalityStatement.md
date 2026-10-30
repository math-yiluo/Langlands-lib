# Local open-restriction criterion for support of algebraic distributions

`Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement.{u}`
is the proposition below. This module only defines the proposition. It
contains no proof, and no published theorem proves it yet (see
[Status](#status)). The module imports the published
`Langlands.HarmonicAnalysis.Distribution.SupportedRestriction`, which brings
in `Distribution.Basic` and `Distribution.Subspace`. None of these modules is
changed.

## Statement

```lean
def OpenRestrictionLocalityStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (Z : Set X) (D : Distribution X),
    (∀ x ∉ Z, ∃ (U : Set X) (hU : IsOpen U),
      x ∈ U ∧ restrictOpen hU D = 0) →
    D ∈ supportedOn Z
```

In words: let `X : Type u` be a topological space in an arbitrary universe
`u` that is Hausdorff (`T2Space X`), locally compact
(`LocallyCompactSpace X`) and totally disconnected
(`TotallyDisconnectedSpace X`). Let `Z : Set X` be any subset and `D` any
algebraic distribution on `X`. Suppose that for every point `x` with
`x ∉ Z` there are an open set `U ⊆ X` and a proof `hU : IsOpen U` such that
`x ∈ U` and the open restriction `restrictOpen hU D : Distribution U` is the
zero distribution. Then `D ∈ supportedOn Z`, that is,

```
D f = 0   for every f : SchwartzBruhat X with f z = 0 for all z ∈ Z.
```

The binder `∀ x ∉ Z, P x` is Lean notation for `∀ x, x ∉ Z → P x`. The
space `X`, its topology and its three topological properties, the subset `Z`
and the distribution `D` are all universally quantified inside the
proposition. The neighborhood `U` and its openness proof `hU` exist
separately for each point `x ∉ Z`, so `U` may depend on `x`. The universe
`u` is the only parameter of the definition.

## Exact meaning of the imported objects

- `SchwartzBruhat Y`, from `Langlands.HarmonicAnalysis.Basic`, is the complex
  vector space of functions `Y → ℂ` that are locally constant
  (`IsLocallyConstant`) and have compact support (`HasCompactSupport`).
- `Distribution Y`, from `Langlands.HarmonicAnalysis.Distribution.Basic`, is
  its full algebraic dual `Module.Dual ℂ (SchwartzBruhat Y)`: every complex
  linear functional, with no topology or continuity condition. For an open
  `U ⊆ X`, `SchwartzBruhat U` and `Distribution U` are the same constructions
  for the subtype `U`, with Mathlib's induced subtype topology.
- `SchwartzBruhat.extendZero hU : SchwartzBruhat U →ₗ[ℂ] SchwartzBruhat X`,
  from `Distribution.Subspace`, extends a test function on the open subtype
  `U` by zero. Its value at `x ∈ U` is the value of the function at
  `⟨x, _⟩`; at `x ∉ U` the value is `0`. It requires `T2Space X`.
- `Distribution.restrictOpen hU : Distribution X →ₗ[ℂ] Distribution U`, from
  `Distribution.Subspace`, is the dual map of `extendZero hU`. Thus
  `restrictOpen hU D f = D (extendZero hU f)` (`restrictOpen_apply`). So
  `restrictOpen hU D = 0` says exactly that `D` vanishes on every zero
  extension of a test function on `U`.
- `Distribution.supportedOn Z`, from `Distribution.Subspace`, is the complex
  submodule of `Distribution X` consisting of those `T` with `T f = 0` for
  every `f : SchwartzBruhat X` such that `f z = 0` for all `z ∈ Z`
  (membership law `mem_supportedOn_iff`). This is support by pointwise
  annihilation. `Z` need not be closed.

The proposition uses exactly these published maps and the published
submodule. It introduces no other notion of support, restriction or
vanishing.

## Scope

- `Z` is an arbitrary subset. It is not assumed closed, open, nonempty or
  proper. The hypothesis is imposed at every point outside `Z`, including
  points of the closure of `Z` that do not lie in `Z`.
- No open cover, family of neighborhoods, finiteness or compactness
  condition is assumed. `X` is not assumed compact, countable,
  second countable or nonempty. Each neighborhood `U` is only open; it may
  be noncompact or all of `X`.
- Empty cases are included. If `X` is empty or `Z = X`, no point lies
  outside `Z`, so the hypothesis holds vacuously. If `Z = ∅`, the
  hypothesis concerns every point of `X`, and by the membership law the
  conclusion `D ∈ supportedOn ∅` says that `D f = 0` for every test
  function `f`.
- `D` is an arbitrary element of the full algebraic dual. No continuity,
  invariance, group action, measure or representation is involved.
- Only one implication is stated. The proposition does not assert the
  converse, and it does not identify `supportedOn Z` with any topological
  support of a distribution. It does not assert any descent of `D` to `Z`,
  any covariance of the published `descendInOpen`, or any orbit-vanishing,
  Shalika-invariance or multiplicity-one statement.

## Provenance

The proposition is internal. It is derived from the existing Library objects
listed above: the actual Schwartz–Bruhat subspace maps `extendZero` and
`restrictOpen`, the full algebraic duals `Distribution`, and the pointwise
support submodule `supportedOn`. It does not transcribe any statement from
the literature, and it cites no source.

It is a locality interface between two ways of saying that `D` lives on `Z`.
One is vanishing of the actual open restrictions near each point outside
`Z`. The other is pointwise annihilation of the test functions vanishing on
`Z`. As motivation only, it is an algebraic counterpart of the usual fact
that a distribution supported in a closed set `C` vanishes on test functions
vanishing on `C`, for example Shalika (1974), Proposition 1.14. That
passage and its relation to the pointwise convention are documented in the
unchanged [ClosedSupportedDescentStatement](ClosedSupportedDescentStatement.md).
Here neither `Z` nor any support is assumed closed, and support is replaced
by the local vanishing hypothesis.

Worker 634 designed this exact proposition as
`Langlands.HarmonicAnalysis.Distribution.Design.OpenRestrictionLocalityStatement`
in the private module `SupportedTransportDesign`. That module is part of the
shared draft revision 8 of the Shalika distribution-invariance task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`. This production module moves the same
proposition, with the same binders, hypotheses and conclusion, into the
ordinary namespace `Langlands.HarmonicAnalysis.Distribution`. The private
`Design` namespace and the other design interface in that module are not
part of this unit.

## Intended proof route

This is the intended later proof. It is not established here, and a
separate exact proof task will follow publication of this statement.

Fix `f : SchwartzBruhat X` with `f z = 0` for all `z ∈ Z`. Every point `x`
of the support `{x | f x ≠ 0}` then lies outside `Z`, so the hypothesis gives
an open `U ∋ x` with `restrictOpen hU D = 0`. In a Hausdorff, locally
compact, totally disconnected space the clopen sets form a basis (Mathlib's
`loc_compact_Haus_tot_disc_of_zero_dim`). So there is a clopen `V` with
`x ∈ V ⊆ U`.

For a clopen `V`, multiplying by the characteristic function of `V` is a
linear cutoff on test functions. Each cutoff `g` of a test function by such a
`V ⊆ U` vanishes outside `U`. Hence it is `extendZero hU φ` for some
`φ : SchwartzBruhat U`, and `D g = restrictOpen hU D φ = 0`. The published
`FiniteOrbitVanishingProof.exists_extension_eq` provides this extension
characterization.

The support of `f` is compact, so finitely many such clopen sets `V` cover
it. Induction over this finite family uses the identity

```
cutoff (A ∪ B) f = cutoff A f + cutoff B f - cutoff A (cutoff B f).
```

It shows that `D` kills the cutoff of `f` by the union. That cutoff equals
`f` itself, because `f` vanishes off the union. Only finite linearity of `D`
is used: no continuity of `D` and no exchange of `D` with an infinite sum or
integral. Empty support, in particular empty `X`, is the base case of the
induction.

Worker 634's private module `OpenRestrictionLocalityCore`, in the same shared
draft revision 8, implements this route as `OpenRestrictionLocalityCore.locality`
for the `Design` copy of the proposition. It adapts the published helper
`exists_extension_eq`, credited to Worker 33 in this task's context, and the
clopen-cutoff and finite-union argument that Worker 121 implemented in the
published `LocalizationProof`. That private file is development
material only. It is not accepted evidence, and it proves nothing about the
production declaration defined here.

## Consumers

The proposition is meant for the final finite-cell argument in Worker 634's
Shalika distribution-invariance task `f79ca82c-d050-4ffa-821b-c347b60e36e0`.
It is also meant for the Whittaker multiplicity-one work of Worker 16 (task
`209cde88-bab8-4a85-8a9d-72b8864b6fa0`).

## Status

This is a statement only. No theorem of type
`OpenRestrictionLocalityStatement.{u}` is published, and nothing in this
module asserts that the proposition holds.

## Authors

Worker 634 designed the proposition. Worker 1080 wrote this production
Lean/Markdown pair.
