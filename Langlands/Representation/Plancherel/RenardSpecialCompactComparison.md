# Comparing the chosen compact quotient with the actual valuation chamber

This internal definition unit records the two explicit geometric obligations
needed to identify the existing compact quotient with the existing norm quotient.
It constructs that identification and transports any actual dominant valuation
section to double-coset representatives, conditional on those obligations.
It does not assert the obligations for arbitrary apartment data.

## Fixed actual objects

The field is any nonarchimedean local field, with the existing `Field`,
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField` instances.
There is no characteristic restriction. The group schemes `S`, `G`, `Z`
and their maps `i : S → G`, `j : Z → G`, `s : S → Z` are actual algebraic
objects. The map `i` has its monomorphism instance and `G` is affine.
The comparison `h : Bijective (restrictionEvaluation s)` is explicit.

For `D : KPApartmentData i (localFieldOrder F)` and `x : D.Apartment`, every
compact subgroup in the declarations is exactly

`K₀ = D.specialCompactSubgroup x = D.compactStabilizer (D.apartmentMap x)`.

Thus it is the common rational-character norm kernel of `G(F)` intersected
with the actual reduced-action stabilizer at the image of `x`. There is no
independent subgroup argument. The definitions are meaningful without proving
compactness. The canonical rational-point topology is inherited from the
existing local-field and building interfaces; no topology is replaced here.

The intended structural specialization has connected reductive `G`, maximal
split `i`, a closed `j` representing `torusCentralizer i`, `s ≫ j = i`,
a generic `ν` specifying the positive relative roots, and a special vertex
`D.IsSpecialApartmentVertex x`. These conditions are not inferred from the
parameters. Full corrected building validity and general existence remain
separate obligations: `KPApartmentData` alone is weaker than those hypotheses.

Write `Zdom = dominantCentralizer i ν s h`. Its inequalities are
`0 ≤ eval S a (centralizerValuation s h z).toAdd` for every positive relative
root `a`. This uses the existing corrected positive character-valuation sign.
The chamber is `dominantValuationImage i ν s h` inside the actual real
valuation image, rather than an asserted full integral cocharacter lattice.

## The comparison properties

`HasSpecialCompactCartanCoverage D x ν j s h` requires that every actual
point of `G(F)` have the same `K₀` double coset as an actual point of `Zdom`.

`HasSpecialCompactValuationClassification D x ν j s h` requires, for
`z,z' ∈ Zdom`, the equivalence

`dominantCompactSetoid D x ν j s h z z' ↔ z' * z⁻¹ ∈ rationalCommonNormKernel Z`.

The left side is the existing induced relation, whose definition is equality
of the actual `K₀` double cosets. The right side uses the actual `Z(F)^1`
norm kernel. `SpecialCompactCartanComparison` is the conjunction of coverage
and classification. These are proposition-valued property definitions, with
no universal assertion that weak apartment data satisfy them.

The two `specialCompactSetoid_iff_*` lemmas reformulate the supplied
classification by equality of real centralizer values and by equality of
integer-character values. They use the existing kernel identities and the
elementary criterion for a quotient of two group elements to lie in the
kernel of a homomorphism.

## Conditional equivalences and representative sets

`dominantCompactNormEquiv` uses the supplied classification to identify the
existing `DominantCompactQuotient` with the existing `DominantNormQuotient`.
It is induced by the identity on dominant actual points, as its class formula
states. No new quotient relation is defined here.

`dominantCompactChamberEquiv` composes that equivalence with the existing
`dominantNormQuotientEquiv`. Its class formula sends the class of `z` to its
actual centralizer value. `dominantChamberDoubleCosetEquiv` then uses coverage
to identify this chamber with `K₀ \ G(F) / K₀`. The value formula explicitly
sends the value of `z` to the double coset of `j(z)`.

For an actual set `A ⊆ Z(F)`, `specialCompactSectionMap` sends each element
to the double coset of its image under `j`. Under
`SpecialCompactCartanComparison` and `IsDominantValuationSection Zdom A`,
`specialCompactSectionMap_bijective` proves this map bijective. Injectivity
uses the classification and injectivity of the valuation section.
Surjectivity first takes a dominant representative by coverage, then takes
the representative with the same value in `A`. The supplied classification
identifies their double cosets. `specialCompactSectionEquiv` packages exactly
this map, with a definitional representative formula.

`SpecialCompactRenardComparison` conjoins the geometric comparison with the
existing `DominantCentralizerLatticeConclusions`. The latter uses the actual
uniformizer subgroup `C0 S s`, its positive part `C0Plus`, finite full
transversals of the quotient by `splitValuationImage s`, and
`tildeC0Plus s F0 Zdom = (C0 S s * F0) ∩ Zdom`. Its dominant-section clause
can be supplied to the representative equivalence above. Its separate
finite positive product cover permits repeated valuation classes. A
chamber-compatible full transversal has the additional rectangular equality
`tildeC0Plus = C0Plus * F0`; only that stronger section supplies a disjoint
parametrization by the product set. Nonrepetition of product pairs is the
separate existing `HasNonrepeatingPositiveProducts` property.

## Scope and provenance

All constructions and proofs here are internal consequences of the existing
actual-object definitions and the explicitly supplied comparison hypotheses.
The quotient equivalence uses `Quotient.congrRight`. The chamber comparison
composes existing equivalences. The section proof uses only the stated
bijection-on-a-set and the two explicit geometric hypotheses. This is not
a proof of a source-facing Cartan decomposition.

The KP parahoric comparison still uses the actual `P_x` and `Z(F)^0`.
The norm kernel and subgroup used here do not identify either of those
objects with `Z(F)^1` or `K₀`. Full corrected building validity, general
existence, compactness and maximality, proof of the two comparison properties,
and inheritance by the same `K₀` in standard Levi subgroups remain separate
targets of the program. This unit does not complete the host task.

Source motivation and normalizations are inherited from the paired public
modules `CentralizerValuation`, `DominantQuotient`,
`SpecialCompactDominantQuotient`, `SpecialCompact`,
`RenardRepresentativeData` and `RenardDominantComparisonStatement`.
Those modules give the original KP and mandatory-correction locators and
the registered July 2026 Renard V.3.23 and V.5.1(4) locators. No additional
source theorem is asserted by this internal transport construction.
