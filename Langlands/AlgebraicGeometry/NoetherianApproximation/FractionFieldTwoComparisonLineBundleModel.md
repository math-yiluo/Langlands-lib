# Fraction-field models preserving two trivial restrictions

This internal construction combines finite-algebra descent of an actual line
bundle with its two trivial restrictions and the compatible normal
fraction-field factorization. It assumes the proposition
`NormalFiniteTypeSubalgebraStatement.{u}` explicitly. It does not prove that
proposition or the valuation-ring extension theorem.

Fix a domain `R` and a chosen fraction field `K` in an arbitrary universe `u`,
with `Algebra R K` and `IsFractionRing R K`. Fix an integer subalgebra `C` of
`R`, schemes `X₀` and `Y₀` over `Spec C`, and two maps `g₁, g₂ : Y₀ → X₀`
over `Spec C`. Let `X` be a scheme over `Spec K` with a map to `X₀`, and
let `M` be an actual Library line bundle on `X`.

`FractionFieldTwoComparisonLineBundleModel` records an integer subalgebra
`T` of `R` containing `C`, with finite generation, integral closedness and
noetherianity. Over the base map `fractionFieldStageBaseMap R C T`, it
records an actual line bundle on
`X₀ ×_(Spec C) Spec (FractionRing T)`. Its restrictions along the base
changes of `g₁` and `g₂` have actual module-sheaf isomorphisms to the
structure sheaf. The model also supplies an actual morphism from `X` to
that product, its two projection equations, a pullback square over the
specified `stageFractionFieldMap R K T`, and an actual sheaf isomorphism
recovering `M` by pullback.

`exists_fractionFieldTwoComparisonLineBundleModel` assumes that `R` is
integrally closed, that `C` is finitely generated over the integers, and
that the supplied `C`-algebra structure on `K` is the composite through
`R`. Both `X₀` and `Y₀` are quasi-compact and quasi-separated over `C`.
The input schemes `X` and `Y` fit into specified pullback squares over
`Spec K`. Two maps `Y → X` respect their structure maps to `Spec K`
and their maps to `X₀` and `Y₀`. The actual bundle `M` has trivial
pullbacks along those two maps. For every finite subset of `R`, the
theorem produces a model as above whose `T` contains that finite subset.
The conclusion asserts existence of actual triviality isomorphisms; it
does not identify them with chosen input witnesses.

The proof first invokes `exists_twoComparisonLineBundleModel`, keeping
all finite algebras over the original `C`. This supplies a finitely
generated `C`-subalgebra `B` of `K`, an actual bundle on the base change
to `Spec B`, both trivial restrictions there, and universal recovery of
`M`. Apply `exists_normal_fractionFieldFactor_over` to `B` and the
prescribed finite ring data. This produces `T`, its normal and
noetherian properties, and an actual ring map `B → FractionRing T`
compatible both with `C` and with the inclusion into `K`.

Contravariance gives the compatible spectrum maps. Use
`TwoComparisonDescent.transition` to pull the bundle from `B` to
`FractionRing T`. Naturality of the two base-changed maps, pullback
composition and the unit comparison pull both trivial restrictions to
this fraction field. The map from `X` is
`TwoComparisonDescent.comparison`; its projection equations follow from
the defining lift, and `comparison_isPullback` proves the asserted
square. Composing it with the transition to `B` gives a map compatible
with both projections, so the original finite-stage recovery applies.
Pullback composition then gives the actual isomorphism recovering `M`.

The provenance is derived from the imported Library constructions and
Mathlib pullback identities. No new literature translation is claimed.
No abelian scheme, self-product, unit axis, compatible rigidification,
correspondence, or extension over the total base is constructed here.
