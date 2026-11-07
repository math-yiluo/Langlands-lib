# Almost-all lifts in the original fixed-base adelic level factors

This derived application implements the cofinite integral-surjectivity
input of Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Theorem 4.5, printed pp.12–13, in the actual
adelic-level products used by `AdelicModelOpenReductionStatement`.

Fix an initial finite set `S`, actual nonaffine schemes `Y` and `B` over
the original ring of S-integers, and a relative morphism `f : Y ⟶ B`.
The assumptions are the full uniform Lang–Weil statement, quasi-compactness
and local finite type over the integers for `B`, and smoothness,
separatedness, surjectivity, local finite type, quasi-compactness and
geometric connectedness for `f`, with every actual fibre of common pure
dimension `d`. The base finite-type condition and the Lang–Weil estimate
are explicit premises; neither is inferred merely from the existence of
the model.

For every enlarged finite set `T` containing `S`, the constructors
`curvePlaceLevelAlmostAllPointLifts` and
`numberFieldLevelAlmostAllPointLifts` return a finite set `E` of actual
local-factor indices. At every index outside `E`, they construct an
actual lift of every relative target point, with the exact equation
`a ≫ f = p` over the original S-integer base. All local rings, coefficient
actions and point types are those already used by the fixed-model
adelic-level construction. The scoped factor-algebra instances restrict
the native T-integer actions along the original S-integer inclusion.

For function fields the factor index is the sum of supported completed
fields and completed integer rings outside `T`. The exceptional index
set is the union of all supported field factors and those integral
factors whose underlying places belong to the finite exceptional set
constructed by `curvePlaceAlmostAllIntegralPointLifts`. For number
fields the exceptional set also contains every original infinite-place
factor. Both collections of field factors are finite. Pulling back the
finite set of exceptional places along the injective subtype projection,
and then mapping into the original sum index, proves finiteness of the
remaining exceptional indices. At any other index the original
coefficient algebra is supplied to the corresponding integral-lift
constructor. No surjectivity at an exceptional factor is asserted.

The corollaries `curvePlaceLevel_eventually_surjective` and
`numberFieldLevel_eventually_surjective` give exactly the cofinite-filter
surjectivity hypotheses for every enlarged level. They follow directly
from the selected lifts outside `E`. All infinite factors remain present
in the number-field index and product; their finiteness permits the
cofinite assertion without imposing a surjectivity premise on them.

This is the arithmetic cofinite input to the fixed-model openness
reduction. It does not prove local openness at any factor, the uniform
Lang–Weil estimate, compatible spreading, the varying-dimension reduction,
or adelic openness for arbitrary spreads. Those obligations remain with
the whole-paper task. The common universe is arbitrary, and the
function-field construction retains both inseparable and separable
presentations over the supplied rational function field.
