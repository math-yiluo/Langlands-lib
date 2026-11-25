# Valuation units of finite completions and their cohomology

This module studies the valuation units of a finite completion of a number
field. It defines the exponent of the normalized valuation on the units of
`E_w`, proves that `F_v`-automorphisms of `E_w` preserve it, and builds the
representation of `Gal(E_w/F_v)` on the valuation units `U_w`. It proves that
`0 → U_w → E_wˣ → ℤ → 0` is a short exact sequence of representations, and
that the induced map `H²(Gal(E_w/F_v), U_w) → H²(Gal(E_w/F_v), E_wˣ)` is
injective. These results hold at every finite place. No unramified hypothesis
is used, and no vanishing of the cohomology of `U_w` is proved.

## The valuation exponent

Let `E` be a number field and `w` a finite place of `E`. On the completion
`E_w = w.adicCompletion E`, Mathlib's valuation `Valued.v` takes values in
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`. A uniformizer has valuation
`WithZero.exp (-1)`.

- `unitsExponent w : E_wˣ →* Multiplicative ℤ` sends a unit `x` to the
  exponent of `Valued.v x`, through Mathlib's `WithZero.unitsWithZeroEquiv`.
  `valued_units` says `Valued.v x = WithZero.exp (toAdd (unitsExponent w x))`.
- `unitsExponent_eq_one_iff`: the exponent of `x` is trivial exactly when
  `Valued.v x = 1`. `toAdd_unitsExponent_neg_iff`: the exponent is negative
  exactly when `Valued.v x < 1`.
- `exists_unitsExponent_eq_neg_one`: some unit has exponent `-1`. It comes
  from Mathlib's `valuation_exists_uniformizer` for `E` and
  `valuedAdicCompletion_eq_valuation'`.
- `unitsExponent_surjective`: the exponent is surjective onto `ℤ`, using
  integer powers of that unit.
- `localUnits w` is the kernel of `unitsExponent w`, the subgroup `U_w` of
  units of valuation `1`. `mem_localUnits_iff` states this membership
  condition.

## Invariance under local automorphisms

Now let `E / F` be an extension of number fields, `v` a finite place of `F`
and `w` a finite place of `E` over `v`. Let `σ` be an `F_v`-algebra
automorphism of `E_w`.

- `valued_localAut_eq_one_iff`: `Valued.v (σ x) = 1` exactly when
  `Valued.v x = 1`. For `x ≠ 0`, `Valued.v x = 1` means that neither `x` nor
  `x⁻¹` lies in the open unit ball. The published `valued_localAut_lt_one_iff`
  says that `σ` preserves the open unit ball.
- `unitsExponent_localAut`: `σ` preserves the valuation exponent of every
  unit. Write `g` for the exponent and `f = g ∘ σ`. Let `π` be a unit with
  `g π = -1`. Then `x π^(g x)` has exponent `0`, so by the previous lemma
  `f x = -(g x) · f π` for every `x`. The unit `σ⁻¹ π` has `f`-value `-1`, so
  `f π` divides `1`. Also `f π < 0` because `σ π` lies in the open unit ball.
  Hence `f π = -1` and `f = g`.

## The representations

- `units_smul_eq_map`: Mathlib's action of `σ` on `E_wˣ` is `Units.map σ`.
  `smul_mem_localUnits`: this action preserves `U_w`.
- `localUnitsAut v w : Gal(E_w/F_v) →* MulAut U_w` is the restricted action.
  `localUnitsAction v w` installs it as a local `MulDistribMulAction`
  instance, and `coe_localUnits_smul` computes it.
- `localUnitsRepresentation v w` is the published
  `NormalizedTwoCocycle.coefficientRepresentation` of this action on
  `Additive U_w`. Its scalars are the published `ULift ℤ`, the same as those
  of the published `unitsRepresentation`.
- `localUnitsInclusion v w : U_w ⟶ E_wˣ` is the inclusion, a morphism to the
  published `unitsRepresentation (padicField v).Carrier (w.adicCompletion E)`.
- `unitsExponentMorphism v w : E_wˣ ⟶ ℤ` is the valuation exponent, a
  morphism to Mathlib's trivial representation on `ULift ℤ`. It is
  equivariant by `unitsExponent_localAut`.
- `unitsValuationSequence v w` is the short complex
  `U_w → E_wˣ → ℤ` formed by these two morphisms. The composite is zero
  because units in `U_w` have exponent `0`.
- `unitsValuationSequence_shortExact`: this short complex is short exact.
  The inclusion is injective. A unit of exponent `0` lies in `U_w`. The
  exponent is surjective by `unitsExponent_surjective`.
- `repShortExact_of_values` is an auxiliary criterion used in the last proof.
  A short complex of representations over any commutative ring and group is
  short exact if its first map is injective, its second map is surjective,
  and every element killed by the second map comes from the first. The proof
  passes to underlying modules with Mathlib's forgetful functor.

## Injectivity in degree two

- `isZero_H1_trivial_integers`: for a finite group `G`, the group
  `H¹(G, ℤ)` with trivial action is zero. Mathlib's `H1IsoOfIsTrivial`
  identifies it with `Hom(G, ℤ)`. A homomorphism `φ` from a finite group to
  `ℤ` is zero, because `|G| • φ x = φ (|G| • x) = 0` and `ℤ` has no torsion.
- `mono_map_localUnitsInclusion_two`: the map
  `H²(Gal(E_w/F_v), U_w) → H²(Gal(E_w/F_v), E_wˣ)` induced by
  `localUnitsInclusion v w` is a monomorphism. In Mathlib's long exact
  sequence (`groupCohomology.mapShortComplex₁_exact`) of
  `unitsValuationSequence v w`, the group before it is
  `H¹(Gal(E_w/F_v), ℤ)`. This group is zero by the previous lemma, because
  `Gal(E_w/F_v)` is finite (`E_w` is finite-dimensional over `F_v` by the
  published `FiniteExtension.local_finite`).

So a `2`-cocycle with values in `U_w` that is a coboundary in `E_wˣ` is
already a coboundary in `U_w`.

## Sources and provenance

Milne, *Class Field Theory* (v4.03, 2020), Chapter III §1, uses the
valuation sequence `0 → U_L → Lˣ → ℤ → 0` of a local field `L` with
Galois group `G` over `K` (the paragraph "The invariant map", printed p. 99,
PDF p. 108). The proof of Proposition 1.1 (printed pp. 97–98, PDF pp.
106–107) uses the unique decomposition `α = u π^m` with `u ∈ U_L` and
`m ∈ ℤ`. Milne works only with unramified extensions there. Here the sequence
is formed at every finite place of a number field. The representation is
built on the actual completion `w.adicCompletion E` with the published
coefficient conventions.

The invariance proof for the exponent, the auxiliary short exactness
criterion and the degree-two injectivity at all finite places are internal.
The injectivity follows from the long exact sequence and the vanishing of
`Hom(G, ℤ)` for finite `G`, and is not stated in this form in the cited
sources.
