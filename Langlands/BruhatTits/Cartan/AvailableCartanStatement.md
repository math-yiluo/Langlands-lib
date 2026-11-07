# Corrected parahoric Cartan bijection under full availability

`AvailableCartanStatement` is a proposition target for Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Theorem 5.2.1 and
(5.2.1)–(5.2.2), printed pp.187–188/PDF pp.218–219, with the mandatory
corrections dated 1 November 2024, PDF pp.24–25 and 30. Registered source
identifiers are `kaletha-prasad-2023-bruhat-tits-new-approach` and
`kaletha-prasad-2024-corrections`. This module states the result and does
not prove it.

## Actual objects and the availability premise

The statement quantifies over every nonarchimedean local field `F`, in either
characteristic, and every actual connected reductive group scheme `G` over `F`.
Its affine instance is supplied by connected reductivity. It uses the existing
local-field topology and the canonical rational-point topology; there is no
replacement topology or restriction to split or quasi-split groups.

Fix an assignment `𝔅 : KPBuildingAssignment` and assume exactly
`𝔅.IsAvailableFor F G hG`. This is the full corrected KP Definition 4.1.26:
the ten axioms of the Library's `FullValidity.Assignment`, including the
comparisons of Axiom 4.1.1 and the field/group isomorphisms of Axiom 4.1.17.
The weaker partial-building and apartment predicates do not replace it.
Availability is required for this `F` and `G`; global `𝔅.IsValid` is not
assumed.

Set `B = (𝔅.datum F G hG).base`. Then `B.i : B.S → G` is the actual
chosen maximal split torus, and `B.centralizer.j : Z → G` represents its
algebraic centralizer on all test schemes. Its actual factor
`s = B.centralizer.s : B.S → Z` satisfies `s ≫ j = B.i`; the data include
the character comparison used to define the valuation.

The target holds for every cocharacter `ν` generic for `B.i`, specifying
`Φ⁺ = positiveRelativeRoots B.i ν`, and every
`x : B.Apartment` with `B.apartment.IsSpecialApartmentVertex x`.
The specialness and vertex conditions are those of the existing actual
affine-root apartment, with its point in the reduced building. The statement
does not choose an unrelated abstract special point or subgroup.

## Positive normalization and the parahoric indexing set

Write `ω_Z = centralizerValuation s B.centralizer.bijective`. Its pairing
with the restriction of a rational character `χ` is the positive normalized
order `ord_F(χ(z))`. For a character of `S` whose multiple `nχ` extends to
`Z`, this gives `ord_F((nχ)(z))/n`, independently of the positive integer
chosen. The actual dominant set is

`D = parahoricDominantSet B ν = {z ∈ Z(F) | a(ω_Z(z)) ≥ 0 for every a ∈ Φ⁺}`.

This agrees with (5.2.1) and with (5.2.2) after reversing its printed
inequality as required by corrections PDF30. The corrections PDF24–25
also fix the positive character-valuation sign. Apartment translation is
the negative projection of this value and is not the dominance map.

The subgroup `P = B.parahoricAt x` is the actual Chapter 7 parahoric,
and `B.centralizerZero` is the actual `Z(F)^0` of KP Definition 2.6.23.
The quotient `ParahoricDominantQuotient B ν` restricts the right-coset
relation to `D`:

`z ∼ z′` if and only if `z′ z⁻¹ ∈ Z(F)^0`.

This is a set quotient. It needs neither normality nor a quotient group
structure. Its equality criterion and the canonical map were constructed
in `ParahoricDominantQuotient`.

## Three conclusions

`ParahoricCartanConclusions B ν x` groups three conclusions on these same
actual objects. The closed target `AvailableCartanStatement` asserts this
property under the preceding availability, genericity and special-vertex
premises.

1. The literal equality of sets is `G(F) = P · j(D) · P`. In Lean the
   left side is `Set.univ` and the right side is the pointwise set product.
   Thus every group point has actual left and right factors in `P` and an
   actual dominant centralizer factor.
2. For all `z,z′ ∈ D`, equality of the double-coset sets
   `P j(z) P = P j(z′) P` is equivalent to `z′ z⁻¹ ∈ Z(F)^0`.
   Both directions are conclusions.
3. The canonical function
   `parahoricDominantDoubleCosetMap B ν x` is bijective from the displayed
   dominant quotient to `P \ G(F) / P`.

The function in the last clause is already well-defined: the intrinsic
inclusion `j(Z(F)^0) ≤ P` proves that changing a representative by this
relation preserves its double coset. Its proved class formula is
`[z] ↦ DoubleCoset.mk P P (j(z))`. Given the asserted bijectivity, the
existing `parahoricDominantDoubleCosetEquiv` packages exactly this map as
an equivalence, with the same formula. The target therefore specifies a
genuine bijection and its representative map, beyond product surjectivity.
No separate well-definedness, coverage or equality-classification premise
is assumed.

## The distinct maximal-compact indexing set

The maximal-compact comparison uses the same geometric point but the
subgroup `K₀ = G(F)^1_x`, represented by
`B.apartment.specialCompactSubgroup x`. Its initial dominant relation is
literal equality of `K₀` double cosets. The separate comparison target
identifies that relation with `z′ z⁻¹ ∈ Z(F)^1`, where
`Z(F)^1 = rationalCommonNormKernel Z`, and with equality of actual
centralizer valuations. Its chamber lies in the actual valuation image.
This module neither substitutes `K₀` for `P` nor substitutes `Z(F)^1`
for `Z(F)^0`. These pairs can differ.

No universal dominant-cocharacter parametrization is imposed. Such an
identification requires additional lattice and component comparisons.
The Renard finite representative sets and the same-`K₀` standard-Levi
comparisons are separate targets.

## Proof and existence boundaries

The three assertions reproduce the corrected theorem and its elementary
quotient consequence. The auxiliary property merely groups conclusions;
it does not make them fields of a supplied building structure. A proof
must establish them from the full availability premise. The correction
on PDF30 replaces the apartment-comparison proof references by
Proposition 4.2.24; no proof using either route is claimed here.

Existence of an assignment or of an available datum is not asserted.
General corrected Bruhat–Tits existence remains a separate prerequisite
program. A future proof of this conditional target is also a separate
successor.
