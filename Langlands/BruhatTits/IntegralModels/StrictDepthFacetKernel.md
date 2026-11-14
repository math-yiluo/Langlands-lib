# Strict-depth sections and the facet reduction kernel

This derived unit defines the subgroup `strictDepthIntegralSections P g D a ψ`
of integral sections whose actual generic points lie in the conjugate by `g`
of the strict-depth subgroup `U_(ψ+)`. The construction is a subgroup map
followed by a subgroup preimage; it assumes no integrality of the whole
strict-depth subgroup.

The data have arbitrary universe `u`. The geometric results use a supplied
parahoric building datum `P`, a maximal-unramified building `C`, an injective
equivariant building map `e`, a zero datum `E`, an apartment subset `Fa`, and
a component model `D` characterized by

```
D.neutral.baseChangeUnramified.integralPoints =
  E.zeroPoints ∩ C.pointwiseFixer (e '' (P.translatedApartmentMap g '' Fa)).
```

They assume the apartment axioms and root reflections, an affine functional
`ψ` with derivative `a`, and one point `y ∈ Fa` with `ψ(y) = 0`. No facet
condition or whole-subgroup integrality is needed.

`conjugated_reflection_not_integral_of_strictDepth` says that any nonidentity
point `x ∈ U_(ψ+)`, with any supplied actual opposite factor pair, has a
nonintegral conjugated reflection. Strict depth gives `0 < y_a(x)` at `y`.
If the reflection were integral, `IntegralFacetReflectionCriterion` would
force its reflection functional to vanish at `y`. The published identification
of that functional with `y_a(x)` gives a contradiction.

`conjugated_strictDepth_mem_positivePoints` additionally assumes the existing
proposition `IntegralOppositeFactorsStatement` as a premise, a closed split
integral torus for the conjugated inclusion, and a reductive quotient `Q`.
For an integral conjugate of `x`, the conclusion is membership in the actual
radical-preimage subgroup `Q.positivePoints`. The identity case is immediate.
For a nonidentity point, choose an actual opposite pair from the parahoric
data and transport it through the inner automorphism. If the middle point
were outside `Q.positivePoints`, the assumed opposite-factor theorem would
make both opposite factors integral. Their product with the middle point
would be an integral actual reflection, contradicting the geometric result.

`strictDepthIntegralSections_le_reductiveReduction_ker` states the same result
on actual integral sections: the defined strict-depth subgroup is contained
in the kernel of `Q.reductiveReduction`. It uses injectivity of the generic
integral-point map and the published identification of this kernel with the
radical preimage.

The provenance is internal: these are consequences of the imported actual
reflection criterion, strict-depth membership formula, group operations,
transport results, and the explicitly assumed opposite-factor statement.
The unit does not prove `IntegralOppositeFactorsStatement`, assert its
availability, identify surviving quotient roots, or prove the host derivative
root-datum theorem. In particular its two kernel conclusions retain that
unproved mathematical input as an explicit premise.
