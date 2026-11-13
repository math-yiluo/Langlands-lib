# Effective finite unramified descent with generic recovery

This internal construction makes the actual finite integer descent datum
effective and recovers the prescribed original generic group. The base F is a
nonarchimedean local field in arbitrary universe `u`. A finite Galois
intermediate field E of its separable closure is supplied, with containment
in the inertia fixed field and the published arithmetic unramifiedness
property. As in `FiniteUnramifiedIntegralDatum`, a `Fact` instance carries
containment for the exact coefficient algebra structures.

The inputs are an actual smooth integral model N over the spectral integers
of E of the E-base change of an F-group G, an actual smooth model P over the
maximal-unramified integers, exact recovery of P from the coefficient base
change of N through the canonical generic tower comparison, the fixed-ring
smooth homomorphism extension property over the maximal-unramified integers,
and stability of P's original integral-point image under every
F-automorphism of the inertia fixed field. No stability of N's own integer
points is assumed.

`finiteIntegralSolution` applies actual affine fpqc effectivity to the
constructed finite integer Čech datum. The finite integer map is flat and
surjective; its affine spectra give quasi-compactness. Affineness of N is
part of the actual model, so the resulting descended group is affine.
`finiteIntegerBaseAut_over` proves that each finite integer automorphism lies
over the norm integer base by the coefficient-algebra commutation identity.

`finiteIntegralSolution_genericCompatible` proves that the prescribed
solution generic comparison respects every canonical generic Galois map. It
finds the small component index for each automorphism, uses the exact
normalized-component recovery of the finite datum and its generic
semilinear law, and invokes the published solution comparison theorem.
This gives actual Galois compatibility, without treating equality of point
sets as a surrogate for generic compatibility.

`finiteDescendedModel` uses the actual affine solution and this generic
compatibility to recover a model over `baseIntegers F` of G itself.
`finiteDescendedModel_smooth` proves smoothness by fpqc descent from N.
`finiteDescendedModelIso` recovers N after finite integer/field coefficient
extension by an actual compatible model isomorphism over the identity of its
specified generic group. The base here is explicitly the canonical norm
integer presentation `baseIntegers F`; conversion to the given valuation
integer presentation is not performed by this unit.

These are internal consequences of the constructed finite datum, actual
affine effectivity, fpqc smoothness descent, normalized-component recovery,
and the existing generic Galois descent comparison. The finite model and its
exact recovery, both smoothness premises, and the fixed-ring extension
property remain supplied. The unit does not establish their existence or
assert the final model comparison over the given valuation integers, and
does not prove KP Fact 2.10.16.
