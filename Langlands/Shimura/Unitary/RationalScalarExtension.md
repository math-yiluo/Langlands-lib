# Rational coefficient comparison and the real Deligne target

Author: Worker 57.

## Purpose and provenance

This internal adapter connects three existing constructions: the rational
coefficient maps in `Coefficients.Algebraic`, the general involution-preserving
tensor-tower equivalence in `InvolutionBaseChangeTower`, and the actual scheme
comparison in `SchemeScalarExtension`. It identifies the real pullback of the
rational similitude group with the existing target in `DeligneGroupScheme`,
including its group structure. No new external theorem is invoked.

The algebraic comparisons are proved by tensor induction and equality of the
unit and scalar coordinates. The geometric comparison is a specialization of
the constructed scalar-extension isomorphism. The Deligne maps are transported
through its inverse, and their comparison identities follow from the actual
isomorphism laws. Thus neither a scheme nor a scheme isomorphism is supplied as
an unconstrained output assumption.

The final specialization uses the previously constructed rational basis and
rational involution of `CentralSimpleUnitaryData`. This adapter does not
construct an identification with an archimedean matrix algebra, a complex
homomorphism for arbitrary CM data, smoothness, reductivity, a PEL moduli scheme,
level schemes, or coefficient local systems. Those remain subsequent tasks.

## Compatibility with the coefficient maps

Let `A` be a possibly noncommutative rational algebra, `L` a field with a
rational algebra structure, and `S` a commutative ring with both rational and
`L`-algebra structures. The two structures automatically form a scalar tower:
Mathlib supplies the rational scalar-tower instance. No compatibility
hypothesis is added here. `L` and `S` share a universe; `A` may lie in another.

`baseChangeTowerEquiv_toAlgHom_eq_towerMap` proves equality of algebra maps

`(baseChangeTowerEquiv ℚ L S A).toAlgHom = towerMap L S`.

Both maps send `s ⊗ a` to `s ⊗ (1 ⊗ a)`. Tensor induction proves equality,
using additivity for sums. The inverse is therefore the already constructed
tensor contraction, which sends `s ⊗ (l ⊗ a)` to `(l • s) ⊗ a`.

For a rational involution `σ`,
`baseChangeTowerSimilitudes_toMonoidHom_eq_towerPoints` proves equality of the
corresponding group homomorphisms. The proof compares their actual algebra-unit
coordinates using the preceding equality and their unchanged scalar units.
`towerPoints_bijective` derives bijectivity of the existing `towerPoints` map
from the equivalence's inverse laws.

`towerPoints_naturality` says that, for an `L`-algebra map `f : S → T`,
applying `pointsMap (f.restrictScalars ℚ)` and then the rational tower map equals
applying the tower map and then `(σ.baseChange L).pointsMap f`. Here `T` has
the same universe as `S`. The proof rewrites both tower maps as the general
similitude equivalence and applies its established coefficient naturality.
These are equalities about the maps already used by the coefficient actions;
the adapter does not redefine those actions.

## The actual real group scheme

For the geometric constructions, `A` and the finite basis index `κ` lie in
`Type 0`, as required by the existing Deligne group-scheme model. Given
`b : Module.Basis κ ℚ A` and `σ : AlgebraInvolution ℚ A`, the definition
`SchemeModel.realScalarExtensionIso` has source

`baseChangedGroupScheme b σ (scalarBaseMap ℚ ℝ)`

and target

`(σ.baseChange ℝ).similitudeGroupScheme (b.baseChange ℝ)`.

The source is the actual categorical pullback along `Spec ℝ → Spec ℚ`.
The target is the existing real coordinate model used for Deligne maps. It is
definitionally the generic `groupScheme` on this extended basis and involution,
so the isomorphism is exactly `scalarExtensionIso ℝ b σ`.

For every scheme `T` over `Spec ℝ`, `realScalarExtensionIso_points` identifies
postcomposition with this isomorphism, under `pointsEquiv`, with
`σ.towerPoints ℝ (restrictedSections ℚ ℝ T)` applied to the pullback's original
point comparison. The local real algebra structure on these global sections is
the one induced by the real structure morphism. The rational action remains
the one induced by its composite with `Spec ℝ → Spec ℚ`. The proof uses the
general all-scheme comparison followed by the proved equality with
`towerPoints`. Affineness of `T` is not assumed.

`realScalarExtensionIso_multiplier` states equality of actual group-scheme
morphisms to the same multiplicative group over the real base: the isomorphism
followed by the new model's multiplier equals `baseChangedMultiplier`.
It specializes the general multiplier square, including its existing
identification of the pullback of the multiplicative group.

## Deligne homomorphisms with the rational pullback as target

Given `h : ComplexHom (σ.baseChange ℝ)`, the definition
`rationalDeligneGroupSchemeMap` composes the existing direct map of group schemes
with `realScalarExtensionIso.inv`. The definition
`rationalInverseDeligneGroupSchemeMap` performs the same transport for the
existing inverse convention. Both land in the actual real pullback of the
rational group. Their `_comparison` theorems say that composing with the
comparison's forward map recovers the original real model maps.

The two `_affinePoints` theorems spell out the old formulas after this
comparison on every real affine test scheme. If `z` is the quadratic unit
corresponding to a point of the Deligne source, the direct map gives
`h.delignePoints S z` and the inverse convention gives
`h.delignePoints S z⁻¹`. The proofs rewrite the commuting comparison and use
the existing Deligne point formulas. They preserve both conventions without
identifying them. The input `h` is algebraic input; its existence for a specified
global algebra is not asserted here.

## Central simple CM specialization

`CentralSimpleUnitaryData.realGroupSchemeIso D` uses the actual
`D.rationalBasis` and `D.toSecondKindInvolution.rationalInvolution`.
Its source is `D.rationalBaseChange (scalarBaseMap ℚ ℝ)` and its target is
the corresponding real `similitudeGroupScheme` on the extended basis.
It inherits the finite-dimensional central-simple CM algebra assumptions and
compatible rational, totally real and CM scalar actions from the existing data
and rational group construction. No real matrix splitting or signature
condition is inferred from this model comparison.
