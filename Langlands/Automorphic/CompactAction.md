# Compact translation on the full automorphic-form space

This is an internal construction from the published `Forms`, `OperatorCore`,
and `CompactTranslationProof` APIs. It bundles the proved compact-preservation
theorem into a representation on the existing full space `AutomorphicForms`.
It introduces no new original-literature identification or analytic hypothesis.

## Parameters and actual action

The field is any `K : Type u` with `Field K` and `NumberField K`, and the rank
is any natural number `n`, including zero. Coefficients are complex numbers.
The acting group is the actual `standardInfiniteCompact K n`, with all its
components; no connected-component restriction is imposed.

`automorphicCompactSubrepresentation` has exactly the submodule underlying
`automorphicSubrepresentation`. It equips that submodule with stability under
the already constructed `finiteSmoothCompactRightAction`. To prove stability,
it translates membership into `IsAutomorphicForm` using
`mem_automorphicSubrepresentation`, applies the published
`automorphicCompactTranslation`, and translates back.

Consequently `automorphicCompactRightAction` is a `Representation` of the
standard infinite compact on the existing `AutomorphicForms K n`. The carrier
is unchanged, and the identity, multiplication, and linearity laws are those
of the restricted actual ambient representation.

`automorphicCompactRightAction_val` identifies its value in the finite-smooth
ambient space. `automorphicToContinuous_compactRightAction` and
`evaluate_automorphicCompactRightAction` identify its continuous-function
realization and evaluation. The convention is positive right translation:

\[
  (R(k)f)(x)=f\bigl(x\,\operatorname{ofInfinite}(k)\bigr).
\]

There is no inverse in this formula. The full existing automorphic conditions
remain in the carrier, including one common center-finiteness condition for
all finite slices and polynomial growth separately on each finite slice.

## Faithful realizations and compact finiteness

`automorphicCompactFiniteSmoothInclusion` is the subtype inclusion into
finite-smooth functions, bundled as an intertwining linear map.
`automorphicCompactContinuousInclusion` is the existing
`automorphicToContinuous`, bundled as an intertwiner into the continuous
infinite-subgroup right action. Both maps are proved injective.

`automorphicCompactRightAction_isFiniteVector` proves that every form is a
finite vector for this compact representation: its complex orbit span is
finite-dimensional. The proof extracts the existing infinite-finiteness
condition from automorphic membership and reflects finite-vector status
through the injective continuous intertwiner using
`FiniteVectors.isFiniteVector_map_iff`.

This is an algebraic finite-vector assertion. No topology on the
automorphic-form carrier or new continuous-representation structure is
introduced.

## Finite translations and the stable core

`automorphicFiniteRightAction_compactRightAction` proves that the existing
finite adelic action commutes with the new compact action on every form.
After applying the injective continuous realization, this is exactly the
published `finiteTranslateIntertwiner` identity, which comes from commuting
finite and infinite adelic factors.
`automorphicCompactFiniteIntertwiner` bundles each compact translation as a
finite adelic intertwiner.

`stableAutomorphicCompactInclusion` uses the same linear inclusion as
`stableAutomorphicInclusion` from the existing operator core into the full
form space. It intertwines `stableAutomorphicCompactAction` with the new
compact action and is injective. Thus the previously defined compact action
on the core agrees with the restriction of the full-space action.

Finally, `automorphicOperatorCore_eq_iff_differential` states

```lean
(automorphicOperatorCore K n).toSubmodule =
    (automorphicSubrepresentation K n).toSubmodule ↔
  AutomorphicDifferentialPreservationStatement K n
```

The proof uses the published two-condition criterion
`automorphicOperatorCore_eq_iff` and discharges its compact-translation clause
with `automorphicCompactTranslation`. It does not discharge differential
preservation. In particular this module does not assert that the full
automorphic space is stable under every enveloping differential operator or
that the operator core already equals the full space.
