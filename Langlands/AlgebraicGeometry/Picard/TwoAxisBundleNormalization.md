# Normalizing an actual bundle along both unit axes

Worker 513 authored this internal construction from the published ordinary
line-bundle class group, projection pullbacks and two-axis adjustment.
It normalizes an existing bundle and recovers an existing restricted bundle
when that restricted bundle has trivial restrictions to both unit axes.

Work in an arbitrary universe `u`. For a Library abelian scheme `A / S`,
write `P = A ×_S A`, `i = (id,e)`, `j = (e,id)`, and `p₁,p₂` for the two
projections. Fix a proof `preservation` of the published canonical pullback
tensor preservation statement. This input can be discharged by the
unconditional theorem `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`.
The ordinary group `LineBundle.IsoClasses preservation P` is used internally.

For an ordinary bundle class `c`, the first correction is

```text
n₁(c) = c / p₁*(i*c).
```

The second correction is

```text
n(c) = n₁(c) / p₂*(j*n₁(c)).
```

The first axis of `n₁(c)` is trivial because `i ≫ p₁ = id`. Its second-axis
restriction becomes trivial after restriction to the unit section, because
`e ≫ i = e ≫ j`. Thus the second correction preserves the triviality on the
first axis: its restriction there factors through that unit restriction.
The second axis of `n(c)` is trivial because `j ≫ p₂ = id`. If both axes of
`c` are already trivial, both corrections are trivial and `n(c)=c`.

Normalization commutes with a map `q : B ×_T B → A ×_S A` and a carrier map
`f : B → A` that commute with the two projections and with the two unit
axes. This is proved solely by pullback composition and the four displayed
commuting-square equalities; no Cartesian or base-change hypothesis is
needed for this part.

`twoAxisNormalizedBundle` chooses an actual Library line bundle representing
`n([E])`. The two `twoAxisNormalizedBundleFirst` and
`twoAxisNormalizedBundleSecond` definitions select actual module-sheaf
trivializations of its axis restrictions. The definition
`twoAxisNormalizedBundleRigidification` applies the existing adjustment to
make those trivializations compatible at the common unit.

Given an existing actual restriction isomorphism `q*E ≅ D`, and actual
trivializations of both axes of `D`, the definition
`twoAxisNormalizedBundleRestrictionIso` returns an actual module-sheaf
isomorphism `q*twoAxisNormalizedBundle(E) ≅ D`. The proof uses naturality of
normalization, its fixed-point property on the class of `D`, and the
ordinary quotient's exact isomorphism relation. Classical choice selects
actual representatives and actual isomorphisms from these proved
existences.

This is internal derived content; it makes no new literature assertion and
introduces no axiom. It does not construct an initial extension `E`, assert
isomorphism preserving preselected rigidifications on `D`, prove
surjectivity on two-axis-rigidified classes, construct a correspondence
representation, or prove extension over arbitrary valuation domains.
