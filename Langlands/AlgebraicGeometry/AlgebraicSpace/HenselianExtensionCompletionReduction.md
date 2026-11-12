# Completion intersection for henselian extension points

Author: Worker 114. This derived supporting unit constructs the completed base-field
inclusion as an algebra homomorphism over the original field and proves the
intersection lemmas used to reduce closedness through completions. The final
closedness reduction and the complete-field closedness theorem are not proved here.
All declarations are in the `ExtensionCompletionReduction` namespace.

## Chart descent

`exists_chart_lift_to_subfield` allows an arbitrary coefficient ring `C`, fields
`k,L` in universe `u` with compatible `C`-algebra structures and scalar tower,
and `separableClosure k L = bottom`. Given an actual etale map from a scheme `U`
over `C` to an algebraic space `X`, an `L`-point of `U` mapping to the extension
of a point of `X(k)` descends to a `k`-point of `U`. There are no topology,
henselianity, separation or quasi-separatedness hypotheses on this lemma.

The proof lifts the `k`-point of `X` to a second actual affine etale chart using
`FieldPointEtaleLift.exists_affine_etale_point`. The represented overlap has an
etale projection to that second chart. The given compatible points define an
`L`-point of the overlap. The published absolute unramified-fibre rationality
lemma descends it to `Spec k`, since `k` is separably closed in `L`. Projection
back to `U` gives the lift, and epimorphy of `Spec L → Spec k` verifies its
structure-map equation over `C`.

## Completed field and affine intersections

For nontrivially normed fields `K,L : Type u` and a normed `K`-algebra structure
on `L`, `completedBaseAlgHom K L` is the continuous completed inclusion
`Completion K → Completion L`, packaged as a `K`-algebra homomorphism. It uses
the published `FiniteExtensionCompletion.map`; no finite-degree assumption is
required by that map. Its compatibility on `K` is `map_coe`.

`mem_range_of_completion_eq` assumes that the image of `K` in `L` is closed. If
`a : Completion K` and `b : L` have the same image in `Completion L`, then `b`
belongs to the image of `K`. Indeed, `a` is in the closure of the original `K`;
continuity of the completed inclusion and the induced topology on `L` put `b`
in the closure of `K` inside `L`. Closedness gives membership.

`exists_affine_point_of_completion_eq` applies this coordinate by coordinate to
actual algebra points in `AlgPoint K A (Completion K)` and `AlgPoint K A L`,
for any commutative `K`-algebra `A`. If all their completed coordinates agree,
it produces a `K`-point extending to the `L`-point. The published
`AlgPoint.range_mapCoefficients` supplies the algebra-map laws. Finite type of
`A` and henselianity are not required.

## Algebraic-space intersection

`exists_point_of_completion_eq` assumes additionally that `L` is henselian and
`X` is separated over `K`. For a point of `X(Completion K)` and a point of `X(L)`
whose images in `X(Completion L)` agree, it produces a point of `X(K)` extending
to the latter point, provided the image of `K` in `L` is closed. There is no
local finite-type, quasi-separatedness or henselianity-of-`K` assumption on this
helper.

The proof lifts the completed-base point to an affine etale chart defined over
`K`. Its image over `Completion L` lies above the given `L`-point. Henselianity
of `L` makes `L` separably closed in its completion, so the chart-descent lemma
produces an `L`-valued lift in the same chart. The affine intersection theorem
then gives a `K`-valued chart point. Injectivity of coefficient change for the
separated space, applied to `L → Completion L`, identifies its image with the
original `L`-point.

These are proved consequences of published actual-point, chart, coefficient,
and completion constructions, with derived provenance and no new source
assertion. The main task retains arbitrary-extension closedness and the exact
whole-statement proof.
