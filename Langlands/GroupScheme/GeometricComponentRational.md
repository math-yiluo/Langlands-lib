# Rational classes in the chosen geometric component group

This is an internal construction from the published actual rational-component
quotient, its injective field-extension map, the full component group over an
algebraically closed field, and the chosen geometric-component action. It adds
no external structural assertion.

Let `k` be a field in arbitrary universe `u`, and let `H` be an actual smooth
affine group scheme over `Spec k`. There is no perfection, characteristic,
connectedness or reductivity premise.

`geometricComponentFixedSubgroup k H` is the subgroup of
`GeometricComponents k H` fixed by every element of the actual absolute Galois
group of `k`. It specializes the published `allComponentFixedSubgroup` to
Mathlib's chosen algebraic closure. Its membership lemma expresses fixedness
using the published scalar action `σ • c`.

`rationalGeometricComponentHom k H` extends the ordinary quotient
`RationalComponentQuotient H` to the chosen algebraic closure, then applies
`allComponentQuotientEquiv` to identify the extended quotient class with its
actual geometric component. The first map is the published
`rationalComponentBaseChange`; it is injective for arbitrary field extensions.
The second map is a multiplicative equivalence. Their composition is therefore
injective.

The projection formula computes this map on every actual rational section `x`:

```
rationalGeometricComponentHom k H (rationalComponentProjection H x)
  = geometricComponentOfPoint k H
      (baseChangeSectionHom (baseMap k (AlgebraicClosure k)) H x).
```

Thus the section is pulled back along the actual coefficient spectrum map.
The formula is definitional from the published quotient and component maps.
The image is fixed by the whole absolute Galois group: represent the class by
a rational section, use the chosen component action formula on sections, and
apply the published fact that coefficient conjugation fixes pulled-back
base-field sections.

`rationalGeometricComponentToFixed k H` factors this same homomorphism through
the fixed subgroup. Its underlying geometric component is unchanged. It is
injective because its composition with the subgroup inclusion is the preceding
injective map.

`geometricComponentOfRationalPoint k H` is the composite of the rational-point
projection with `rationalGeometricComponentHom`. Its application formula is
the actual-section formula above. Its kernel is exactly
`rationalIdentitySubgroup H`, the subgroup of sections coming from the actual
identity-component subgroup scheme. The proof uses injectivity of
`rationalGeometricComponentHom` to reduce the kernel equation to that of the
published rational quotient projection. A corresponding equality-to-one
criterion is supplied.

The image characterization `mem_range_rationalGeometricComponentHom` says
that a geometric component lies in the image precisely when it is the component
of a section pulled back from `H(k)`. For the forward implication, represent the
quotient class by a rational section and use the projection formula. For the
reverse implication, use that section's rational quotient class.

For an actual group-scheme homomorphism `f : H ⟶ H'` over `k`, with both groups
smooth and affine, `geometricComponentMap_ofPoint` identifies the chosen
component map with the actual pulled-back section map. Its proof unfolds to
the published continuous map on the actual scheme components.
`geometricComponentFixedMap k f` restricts the component homomorphism to the
fixed subgroups. Its membership proof uses `geometricComponentMap_smul` and
the source component's fixedness. The value, identity and composition laws
follow from those of `geometricComponentMap`.

The two naturality laws state

```
geometricComponentMap k f (rationalGeometricComponentHom k H c)
  = rationalGeometricComponentHom k H' (rationalComponentMap f c)
```

and the same equation with the fixed-subgroup factorizations. The first proof
represents `c` by a rational section and combines the component section formula
with naturality of `baseChangeSectionHom`. The second applies equality of
subtypes to that equation.

The rational quotient here is the ordinary quotient of groups of rational
sections by the identity-component sections. No equality with the whole
Galois-fixed component subgroup is asserted, and no surjectivity onto that
subgroup, effective descent, or fppf quotient realization is claimed.
