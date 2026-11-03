# Actual affine section maps under generic base change

This internal module defines `pullbackSectionAlgebra` from the actual
section map `q.app U` of a scheme morphism. It equips the actual sections
on `q ⁻¹ᵁ U` with their algebra structure over the actual sections on `U`.

For any commutative ring `R`, any supplied fraction field `K`, and any actual
cartesian square exhibiting `q : Y → X` as the base change of
`Spec K → Spec R`, `isLocalization_pullbackSectionAlgebra` proves that
this actual section map, over an affine total open, is localization at
the images of the non-zero-divisors of `R`. The coefficient algebra on
the total sections is the imported `affineSectionAlgebra` derived from
the actual map `X → Spec R`. No valuation or Noetherian assumption is
needed.

The proof restricts the cartesian square to the affine total open. Its
inverse image is affine because the generic projection is affine. The
canonical affine-chart isomorphisms give a pullback square of spectra,
and full faithfulness of the spectrum functor reflects it to a pushout
square of actual ring homomorphisms. The localization base-change
criterion then proves the stated localization property. The provenance
is internal, using Mathlib's affine duality, categorical pullbacks and
localization base change.
