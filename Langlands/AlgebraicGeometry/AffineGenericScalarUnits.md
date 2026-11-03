# Compatible scalar units on actual affine generic opens

This internal construction uses a domain `R`, the supplied fraction field `K`,
and an actual cartesian square whose bottom map is `Spec K → Spec R`.
For an affine total open `U`, `affineGenericScalarUnit` turns a nonzero
scalar `r : R` into a unit on the actual inverse image `q ⁻¹ᵁ U`.
The actual section map is the localization at nonzero base scalars by
`isLocalization_pullbackSectionAlgebra`; `IsLocalization.map_units`
therefore supplies the unit. Its value is exactly the image of `r` under
the coefficient algebra map followed by `q.app U`.

For affine `V ≤ U`, `affineGenericScalarUnit_restrict` proves compatibility
with the original generic section restriction. Its proof uses the
coefficient compatibility of `affineSectionRestrictionAlgHom` and
naturality of `q.app`. The definition `affineGenericScalarRatio` takes
nonzero `r,d : R` and forms the unit represented by `d/r`; the subsequent
lemma proves that these ratios also commute with restriction.
These constructions and restriction identities need neither smoothness
nor projectivity.

Assume further that `R` is a valuation domain, that the structure morphism
`p` is smooth with geometrically connected fibres, and that `U` meets the
closed fibre. The definition `affineGenericUnitDecomposition` additionally
requires projectivity of the actual `R`-module `Γ(X,U)`. It applies the
published projective scalar decomposition to the actual section
localization, using `closedFibreIdeal_isPrime_affineSectionAlgebra` for
the required prime ideal. The output records a nonzero denominator `r`,
a nonzero numerator `d`, a total unit `a`, and the cleared equation
`q(r) * b = q(d) * q(a)`.

The lemma `affineGenericUnitDecomposition_eq` identifies the original
generic unit exactly as the scalar ratio `d/r` times the image of `a`
under the original map `q.app U`. Its implemented proof cancels the
denominator in the unit group, reorders the commuting units, and checks
the resulting value equality using the recorded cleared equation.
It does not use an inverse operation on the underlying section ring.

The provenance is internal: this module packages the published actual
section localization, affine restriction algebra map and projective
valuation-algebra decomposition, and proves their compatibility using
Mathlib's unit-group operations. It asserts no geometric projectivity
result and constructs no global bundle; projectivity remains an explicit
input to the decomposition.
