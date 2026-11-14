# Actual integral reflection representatives for descended facet models

This derived unit constructs actual reflection representatives for a supplied
descended model, at arbitrary universe `u`. It uses a supplied parahoric building
datum `P`, its apartment axioms and root-reflection property, an equivariant map
`e` to a supplied maximal-unramified building `C`, and a supplied unramified zero
datum `E`. The subset `Fa` may be any apartment subset. For the integral
construction, the supplied relative-component model `D` satisfies the exact
image identity

```
D.neutral.baseChangeUnramified.integralPoints =
  E.zeroPoints ∩ C.pointwiseFixer (e '' (P.translatedApartmentMap g '' Fa)).
```

No smoothness of `D`, injectivity of `e`, or facet condition is needed for these
reflection results. The definition additionally takes an integral torus `T`
with generic inclusion `P.i ≫ (G.innerIso g).hom` and `T.IsClosedSplit`, a supplied
special-fibre quotient `Q`, arbitrary relative-root reflection data `Droot`
for `P.i`, and a root `a` whose character belongs to `facetDerivativeRoots P Fa`.
The quotient need not satisfy reductive-quotient validity for this construction.

`facetReflectionQuotientRepresentative` returns a pair consisting of an actual
rational point `n` of `Q.quotient` and an automorphism `σ` of `T.specialFibre`,
together with:

- the actual normalizer square
  `IsNormalizingPoint (T.specialFibreInclusion ≫ Q.projection) n σ`;
- for every character `χ` of `T.specialFibre`, the formula
  `characterAut σ χ = χ - ⟨χ, coSpec (Droot.coroot a)⟩ • charSpec a`.

Both specialization maps are the canonical maps through this same integral
torus. The construction starts with an actual integral section and maps its
reduction through `Q.projection`; it uses no assertion of surjectivity on
rational points.

The proof first establishes
`rationalExtend_mem_zeroPoints_of_mem_simplyConnectedImage`. The supplied
simply connected derived cover is base changed to the inertia fixed field.
Published reductivity, derived-subgroup and simply-connected-cover base-change
results make it a simply connected derived cover of the extended group.
Independence of the cover image identifies it with the cover image in `E`.
An actual lift point extends by scalar extension, so the extended point lies
in that image and hence in `E.zeroPoints`.

For `exists_facetReflection_normalizer`, an affine root vanishing on `Fa`
has a nontrivial filtration jump. Injectivity of root forms identifies its
root with `a`. A point in the jump and the published opposite-factor-pair
existence give the actual generic reflection element `P.reflectionElement hp`.
The apartment axioms place it in the simply connected image; the supplied
root-reflection property makes it fix `Fa`. Its factor-pair coroot is identified
with `Droot.coroot a` using pairing two, equality of the full character actions,
and finiteness of the actual Weyl image of the split torus. Thus the result
uses the prescribed coroot in the full character formula.

`conjugated_normalizer_mem_integralPoints` transports the simply connected
image through `G.innerIso g`. Equivariance of `e` and compatibility of the
normalizer action with the apartment chart show that this conjugated point fixes
the image of the translated subset. The displayed model identity places its
scalar extension in the base-changed integral-point image. The published
maximal-unramified integral-point descent equivalence puts the original point
in `D.neutral.integralPoints`, the image of actual integral sections.

`exists_integral_facetReflection` chooses such a section. Transport of its
generic normalizer square by the ambient inner isomorphism leaves the torus
unchanged, and hence retains the same character formula. Finally,
`IntegralTorusNormalizer` extends this generic torus automorphism to `T` and
specializes it by residue base change. Its normalizer-specialization theorem
gives the actual quotient point, and its pairing-preserving reflection theorem
gives the displayed special-fibre formula. Classical choice selects the pair
with both properties.

This is derived content assembled from the named published building,
group-scheme, and integral-model results and the supplied hypotheses. It is a
reflection prerequisite for the derivative root-datum assertion. It does not
identify which characters are roots of the reductive quotient and does not
assert `UnramifiedFacetRootDatumStatement`.
