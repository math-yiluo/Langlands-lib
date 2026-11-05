# Integral Weil generic fiber of the original projective scheme

This derived construction connects the actual arithmetic models to the Weil
restriction of the originally specified field scheme in Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), Example 4.2, printed pages 9–10.
Its target is the Weil scheme of the original X with its specified projective
immersion and resulting field structure map.

The general `projectiveModelWeilGenericFiberIso` takes actual constructed
projective-immersion model data over an integral-closure coefficient ring B of
A in the original upper field L. The original lower field K is the fraction
field of A, L is finite over K, and B is finite projective over A. It first
identifies the original-field generic fiber of the integral Weil model with the
field Weil restriction of the upper model's generic fiber. The constructed
model's canonical `genericFiberIso` identifies that generic fiber with the
original X. The actual target-isomorphism construction for Weil restriction
then gives an isomorphism to the Weil restriction of the original X. Model
geometry is derived from the specified projective immersions; no additional
separatedness or finite-affine-neighborhood package is assumed.

The general all-test comparison proves equality with the specified integral
counit comparison followed by the constructed model's original-field
isomorphism. It follows by the two already proved counit comparisons: first
naturality of the actual Weil target isomorphism, then the integral-closure
generic-fiber comparison. This retains the original point maps on every test
scheme over K.

`numberFieldProjectiveModelWeilGenericFiberIso` instantiates this construction
with the actual lower number-field S-integers and the actual upper S-integers
at the full exceptional preimage from the constructed extension-compatible
model data. All integral-closure, finiteness, projectivity and original
fraction-field hypotheses come from `NumberFieldSIntegerFinite`.

`curvePlacePrincipalProjectiveModelWeilGenericFiberIso` instantiates it with
the actual curve principal exceptional set selected by
`CurvePlacePrincipalProjectiveModelData`, and its full upper inverse image.
The recorded nonzero denominator supplies the exact nonzero `Fact`; the
arithmetic properties are the derived instances of
`CurvePlacePrincipalSIntegerFinite`. The actual constructor
`curvePlaceFunctionFieldProjectiveModel` produces such data from any original
quasi-compact projective immersion and prescribed finite supports. Thus the
function-field specialization requires neither assumed finiteness data nor
separability of the original finite extension.

All rings and fields inhabit an arbitrary common universe. The general helper
states its integral-closure arithmetic hypotheses explicitly; the two actual
arithmetic specializations instantiate them from proved constructions. The
curve specialization uses finite constants and the proved cofinal principal
family. The adelic topological comparison remains an obligation of the host
task.
