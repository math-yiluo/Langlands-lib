# Charts of translated apartments

This is an internal construction for one supplied
`ValuationBuildingData G`, over the same nonarchimedean local field and actual
connected reductive group as the data. Both mixed and equal characteristic
remain permitted. It contributes a coordinate calculation toward KP Axioms
4.1.1 and 4.1.4, and does not prove those axioms in full.

## Provenance

The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Axioms 4.1.1 and 4.1.4, printed pp.157–159 (PDF pp.188–190), read
together with the authors' corrections of 1 November 2024, Chapter 4
(PDF p.27). The registered source IDs are
`kaletha-prasad-2023-bruhat-tits-new-approach` and
`kaletha-prasad-2024-corrections`. The corrections do not change A2.

The definitions and short lemmas here are derived from the published
`ValuationBuildingData` action and its actual normalizer action. They are
coordinate constructions, rather than a claim that KP's general building
exists.

## Implemented constructions

`translatedApartmentMap g` is the map
`x ↦ g • B.apartmentMap x` into the actual reduced building. Its range is
`g • B.apartmentImage`. It is injective if the base apartment map is
injective; `translatedApartmentChart` then gives an equivalence with the
subtype of points in this range. This equivalence is a type equivalence.

Under `HasNormalizerApartmentStabilizer`, the two translated images for
`g` and `h` agree precisely when `h⁻¹g` belongs to the actual subgroup
`normalizerPoints B.i`. This is the usual normalizer-coset condition, with
the left-coset convention fixed by the displayed formula.

`normalizerCosetApartmentEquiv` is a bijection from
`G(F) / normalizerPoints B.i` to the subtype of actual building subsets
satisfying `B.IsApartment`. It sends the class of `g` to
`g • B.apartmentImage`. Its representative formula and compatibility with
left translation by every element of `G(F)` are proved. This indexing
equivalence requires the stabilizer condition, but does not require
injectivity of the base apartment map.

Whenever that membership holds, `apartmentChartTransition g h` is the
published affine normalizer action of `h⁻¹g` on `B.Apartment`. The target
chart composed with this transition equals the source chart. Its linear
part is `translationAction B.i (h⁻¹g)`, the published action on
`TranslationSpace B.i`, the quotient of real cocharacters by the common
root kernel. Identity and composition of transitions are proved using
the normalizer action homomorphism.

## Proof route and remaining boundary

Range and injectivity follow from the group action and the corresponding
base-map properties. The coset criterion follows by acting by `h⁻¹` and
using the specified apartment stabilizer. The indexing equivalence is
Mathlib's orbit–stabilizer equivalence for the action on subsets,
transported along that stabilizer equality and the definition of
`B.IsApartment`. Equivariance follows by quotient induction and the
group-action multiplication law. The transition formula is
normalizer equivariance of the base apartment map. The derivative formula
is the published normalizer action's linear-part formula. Composition
uses `(k⁻¹h)(h⁻¹g) = k⁻¹g`.

No affine structure on the apartment subtype is installed by the type
equivalence alone. No bijection with actual maximal split subtori is
constructed here. In particular, this unit does not identify the vector
space of a translated apartment with the real cocharacters of its actual
conjugate torus, and does not supply A2's natural derivative between two
such spaces. Those comparisons, the existence of the supplied data,
the stabilizer hypothesis, base-map injectivity and the full corrected
Definition 4.1.26 remain separate obligations.
