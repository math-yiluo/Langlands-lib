# Actual quasi-projective curve models on principal arithmetic levels

This derived construction implements the function-field model-existence step
of Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Example
4.2, printed pages 9–10, with the arithmetic levels needed for integral Weil
restriction. Given the original finite extension, a quasi-compact scheme X with
a specified immersion into projective space over the original upper field, and
prescribed finite lower and upper exceptional sets, it constructs an actual
model over the full upper preimage of a principal lower exceptional set.

`CurvePlacePrincipalProjectiveModelData` records the nonzero denominator in the
normalized lower parameter chart, containment of both prescribed exceptional
sets, and actual `ProjectiveImmersionRingModelData` over the precise upper
S-integer ring. The geometric data include the same-dimensional immersion,
local finite presentation and quasi-compactness of its structural map, the
Cartesian square with the original upper field, and the equality retaining the
specified original projective map. The corresponding lower and upper rings
have already been proved to form a finite locally free extension in
`CurvePlacePrincipalSIntegerFinite`; those properties are derived from the
chosen denominator, rather than assumed geometric data.

`curvePlacePrincipalProjectiveModel` first derives the upper function-field
presentation from the original lower one and the finite extension. The proved
finite coefficient-model construction supplies the original scheme and
immersion over a finitely generated integer subalgebra of the upper field.
Finite-pole exhaustion puts all its generators in one upper S-integer stage,
also containing the requested upper support. Adjoining the restrictions of this
finite upper support to the requested lower support gives one finite lower set.
The proved principal-level cofinality supplies a nonzero chart denominator whose
actual exceptional set contains that lower set. The original coefficient
subalgebra therefore lies in the upper S-integer ring at its full preimage.
The literal coefficient inclusion and original upper-field inclusion form the
required scalar tower. `projectiveImmersionCoefficientBaseChange` constructs
the actual geometric model and both retained original-field comparisons.

`curvePlaceFunctionFieldProjectiveModel` derives the parameter itself from the
image of the rational-function variable in the original lower field. The
given function-field presentation proves finite degree over its generated
subfield, so this constructor needs no separately supplied parameter or upper
function-field presentation.

All fields inhabit an arbitrary common universe. Finite constants and the
compatible finite original extension are explicit. No separability assumption
is imposed. Both prescribed finite exceptional sets may be empty, and the
projective dimension is any natural number, including zero. Quasi-compactness
and the specified projective immersion are the geometric inputs. The original
Weil-model generic-fiber comparisons are available separately; the adelic
topological comparison remains an obligation of the host task.
