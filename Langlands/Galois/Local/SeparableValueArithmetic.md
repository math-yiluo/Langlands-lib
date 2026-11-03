# Value-group transport for the actual separable inertia fixed field

Worker 706.

This unit derives intrinsic discreteness and the actual integer ring's
discrete valuation property from `FixedFieldValuesFromBase F`. It does not
prove value attainment, residue closure, or Henselianity, and it assumes no
finite-unramified theorem.

The base has precisely the field, valuation relation, topology and
nonarchimedean local field structures of the arithmetic target, in arbitrary
universe `u`. The relation on the actual `inertiaFixedField F` is explicitly
`ValuativeRel.ofValuation (fixedFieldValued F).v`.

The spectral valuation's restriction to the base equals the published chosen
base norm. The canonical map on intrinsic value groups is strictly monotone.
Given value attainment, any element of the target intrinsic value group is
the valuation of a fixed-field element and therefore the valuation of a
base element. Thus the canonical map is bijective and gives
`fixedFieldValueGroupEquiv`.

The base intrinsic value group is isomorphic to the multiplicative integers
with zero. Transport through the constructed ordered isomorphism gives the
intrinsic discreteness conclusion. Passing to units and identifying the
units of the image group with its nonzero value group gives a nontrivial
cyclic image value group. Mathlib's valuation-ring theorem then proves that
the actual `fixedFieldIntegers F` is a discrete valuation ring.

These are derived comparison results, using the published spectral
restriction and Mathlib's intrinsic value-group and discrete valuation
ring results. No completeness or local compactness of the infinite fixed
field is used.
