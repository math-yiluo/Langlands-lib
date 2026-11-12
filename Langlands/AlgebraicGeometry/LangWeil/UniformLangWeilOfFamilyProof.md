# Proof: Conrad's Lemma 4.6 from the uniform Lang–Weil estimate in families

Author: Worker 185.

This module proves the published statement
`Langlands.AlgebraicGeometry.LangWeil.UniformLangWeilOfFamilyStatement` with the theorem
`Langlands.AlgebraicGeometry.LangWeil.uniformLangWeilOfFamily`. It imports the statement's
Lean/Markdown pair unchanged and adds no hypotheses. The theorem takes the family estimate
`FamilyLangWeilStatement` as the antecedent of the implication. It assumes no Lang–Weil,
Hasse–Weil, Weil-conjecture or Bertini input beyond that. The derivation follows the route in
the statement's Markdown. It uses three auxiliary results, each proved in this module.

## Geometric irreducibility

`geometricallyIrreducible_of_smooth_of_geometricallyConnected` proves that a smooth,
geometrically connected morphism `f : Y ⟶ B` is geometrically irreducible. By Mathlib's
definition, this means that every pullback `Z` of `f` along a morphism `Spec K ⟶ B`, with `K` a
field, is an irreducible space. For such a pullback square, the projection `Z ⟶ Spec K` is
smooth by base change (`MorphismProperty.of_isPullback`). It is therefore locally of finite
type, so `Z` is locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`). `Z` is
connected because `f` is geometrically connected. The Library theorem
`Langlands.AlgebraicGeometry.smoothDomainStalks` shows that all stalks of `Z` are domains.
The Library theorem `Langlands.AlgebraicGeometry.connectedLocallyNoetherianDomainStalksIntegral`
then shows that `Z` is integral. An integral scheme is irreducible. This argument follows
the Library proof `Langlands.AbelianScheme.smoothGeometricIntegrality`.

## Finite residue fields at closed points

`finite_of_moduleFinite_int` proves that a field `K` that is finitely generated as a module
over `ℤ` is finite. Let `p` be the characteristic of `K`.

- If `p` is prime, `K` is a `ZMod p`-algebra. It is finitely generated as a
  `ZMod p`-module (`Module.Finite.of_restrictScalars_finite`), so it is finite
  (`Module.finite_of_finite`).
- If `p = 0`, then `ℤ → K` is injective and `K` is integral over `ℤ`. Since `K` is a field,
  `ℤ` would then be a field (`isField_of_isIntegral_of_isField`), which is false
  (`Int.not_isField`).

`finite_residueField_of_isClosed` proves that `κ(b)` is finite for each closed point `b` of a
scheme `B` locally of finite type over `Spec (ULift ℤ)`. Because `{b}` is closed, the morphism
`B.fromSpecResidueField b` is a closed immersion (`isClosed_singleton_iff_isClosedImmersion`).
Its composite with the structure morphism to `Spec (ULift ℤ)` is therefore locally of finite
type. This composite is `Spec.map φ` for some ring homomorphism `φ : ULift ℤ → κ(b)`, and `φ` is
of finite type (`HasRingHomProperty.Spec_iff`). Precomposing with the ring isomorphism
`ℤ ≃+* ULift ℤ` gives that `κ(b)` is a finitely generated `ℤ`-algebra. All ring homomorphisms
out of `ℤ` are equal, so this is the canonical algebra structure. The Library theorem
`Langlands.AlgebraicGeometry.NoetherianApproximation.isJacobsonRing_int` shows that `ℤ` is a
Jacobson ring. Zariski's lemma for Jacobson rings (`finite_of_finite_type_of_isJacobsonRing`)
then makes `κ(b)` a finite `ℤ`-module, hence a finite field by the previous result.

## Fibre sections and lifts

`fiberSectionEquiv f b` is an explicit bijection between

- sections `s : Spec κ(b) ⟶ f.fiber b` with `s ≫ f.fiberToSpecResidueField b = 𝟙`, and
- morphisms `x : Spec κ(b) ⟶ Y` with `x ≫ f = B.fromSpecResidueField b`.

Mathlib defines `f.fiber b` as the pullback of `f` along `B.fromSpecResidueField b`, with
`f.fiberι b` and `f.fiberToSpecResidueField b` the two projections. The forward map sends `s`
to `s ≫ f.fiberι b`; it satisfies the required equation by `Scheme.Hom.fiber_fac`. The inverse
sends `x` to `pullback.lift x (𝟙 _)`. The two maps are mutually inverse by the universal
property of the pullback (`pullback.lift_fst`, `pullback.lift_snd`, `pullback.hom_ext`).

## The main theorem

Let `f : Y ⟶ B` and `d` satisfy the hypotheses of `UniformLangWeilStatement`. By the first
result, `f` is geometrically irreducible. The hypotheses of `FamilyLangWeilInDimension d` for
`S = B`, `X = Y` and this `f` are then available: `B` is locally of finite type over the
integers and compact, `f` is locally of finite type and quasi-compact, and every fibre has pure
dimension `d`. The family estimate gives a constant `C > 0`. Let `b` be a closed point of `B`.
Its residue field `κ(b)` is finite by the second result. Apply the family estimate with
`κ = κ(b)` and the canonical point `s = B.fromSpecResidueField b`. The bijection
`fiberSectionEquiv f b` identifies the count `N_b` of the target statement with the count of
lifts `x` with `x ≫ f = s`, by `Nat.card_congr`. The inequality is then exactly the family
estimate at `(κ(b), s)`, with the same constant `C`.

The hypotheses that `f` is separated and surjective are not used. The quasi-compactness of
`B` and of `f` are used only to supply the corresponding hypotheses of the family estimate.
