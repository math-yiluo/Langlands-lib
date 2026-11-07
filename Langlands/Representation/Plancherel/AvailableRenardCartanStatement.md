# Actual maximal-compact Cartan and standard-Levi comparison

`Langlands.Plancherel.RenardCartan.AvailableRenardCartanStatement` is the
conditional actual-group statement target for the Cartan and lattice
comparisons used in Renard V.5.1(4),(5), with the representative definitions
of V.3.23. It concludes both the ambient comparison and its compatibility
inside every actual standard Levi. This module states the target and
does not prove it.

## Full local availability and the fixed actual objects

The quantifiers allow every nonarchimedean local field `F`, in mixed or
equal characteristic, and every actual connected reductive group scheme
`G` over `F`. Connected reductivity supplies the affine instance.
The local-field topology and the canonical rational-point topology are
the existing ones; no split, quasi-split, tame or residue-characteristic
restriction is imposed.

Fix `𝔅 : KPBuildingAssignment` and assume `𝔅.IsAvailableFor F G hG`.
This is exactly the full corrected KP Definition 4.1.26 predicate in
`FullValidity.Assignment`, with all ten axioms, including the comparisons
of Axiom 4.1.1 and the field/group isomorphisms of Axiom 4.1.17.
The statement does not replace it with the partial building axioms or
the weaker `KPApartmentData` predicate. It needs local availability for
this field and group, and does not require global `𝔅.IsValid`.

Set `B = (𝔅.datum F G hG).base`. The torus `B.i : B.S → G` is the
chosen actual maximal split torus. The map `j = B.centralizer.j : Z → G`
is a closed representative of its whole algebraic centralizer on all
test schemes, and `s = B.centralizer.s : B.S → Z` satisfies `s ≫ j = B.i`.
The character comparison is the actual `B.centralizer.bijective`.
These data are inherited from the assignment; no independent
conclusion-bearing subgroup or centralizer is supplied.

For every cocharacter `ν` generic for `B.i`, take
`Φ⁺ = positiveRelativeRoots B.i ν`. For every `x : B.Apartment` satisfying
`B.apartment.IsSpecialApartmentVertex x`, fix exactly

`K₀ = B.apartment.specialCompactSubgroup x
    = G(F)^1 ∩ G(F)_{B.apartmentMap x}`.

Here `G(F)^1 = rationalCommonNormKernel G` and the second factor is the
stabilizer for the actual reduced-building action. This is the geometric
subgroup shared with the special-compact and Iwasawa statements.
There is no new choice of a compact subgroup.

## Ambient relation, chamber and representative bijections

Write `ω_Z = centralizerValuation s B.centralizer.bijective` and
`D = dominantCentralizer B.i ν s B.centralizer.bijective`.
The normalization is the corrected positive character order,
`χ(ω_Z(z)) = ord_F(χ(z))`, with the uniformizer of order `+1`.
Thus `D` consists of actual `z ∈ Z(F)` with
`a(ω_Z(z)) ≥ 0` for every `a ∈ Φ⁺`. The negative projected valuation
governs apartment translation; it is not used for dominance.

The first conclusion is `SpecialCompactRenardComparison` for these exact
`B.apartment`, `x`, `ν`, `j`, `s` and character comparison. Unfolding it
gives both of the following geometric assertions and the lattice
conclusions described below:

1. Every `g ∈ G(F)` has the same `K₀` double coset as `j(z)` for an
   actual `z ∈ D`.
2. For `z,z′ ∈ D`, equality of their `K₀` double cosets is equivalent
   to `z′ z⁻¹ ∈ Z(F)^1`, where
   `Z(F)^1 = rationalCommonNormKernel Z`.

The left relation is the already defined induced relation
`dominantCompactSetoid`: literal equality of the actual double-coset
classes. The existing `specialCompactSetoid_iff_valuation_eq` and
`specialCompactSetoid_iff_characterValue_eq` identify it with equality
of the real centralizer values and of the integer-character values.
These are consequences of the concluded classification.

Consequently the existing `dominantCompactNormEquiv` identifies the
induced quotient with the restricted right quotient by `Z(F)^1`.
The existing `dominantChamberDoubleCosetEquiv` identifies the actual
chamber `dominantValuationImage B.i ν s B.centralizer.bijective` with
`K₀ \ G(F) / K₀`, with formula `ω_Z(z) ↦ K₀ j(z) K₀`.
Its chamber lies in the actual valuation image, rather than an assumed
full integral cocharacter lattice.

For any actual dominant valuation section `A ⊆ Z(F)`, the existing
`specialCompactSectionMap_bijective` and `specialCompactSectionEquiv`
give a bijection by the same representative map `a ↦ K₀ j(a) K₀`.
They include injectivity and surjectivity; product coverage alone is
not the asserted relation classification.

## Renard's actual finite representative data

The lattice component is exactly
`DominantCentralizerLatticeConclusions B.i ν s B.centralizer.bijective`.
All its sets are the existing actual-object definitions in
`RenardUniformizerSection` and `RenardRepresentativeData`:

- `C0 B.S s` is the image in `Z(F)` of the actual cocharacter
  uniformizer section of `B.S(F)`.
- `C0Plus B.S s Φ⁺` is its positive uniformizer part.
- A full finite transversal `F0` is a finite set of actual points of
  `Z(F)` whose lattice residues biject onto the quotient of the actual
  integer-character image by `splitValuationImage s`.
- `tildeC0Plus s F0 D = (C0 B.S s * F0) ∩ D` is Renard's dominant
  representative set, using the full uniformizer group before the
  chamber intersection.

The concluded predicate asserts the uniformizer formula
`ω_Z(s(c(π))) = 1 ⊗ c`, the equality `C0Plus = C0 ∩ D`, and the
comparison of the real and integer-character chamber images by
`centralizerValuationImageEquiv`. It asserts a finite full transversal
contained in `D`. For every full finite transversal, its `tildeC0Plus`
is a dominant valuation section and bijects onto the real chamber.
The representative map above therefore gives a disjoint, exhaustive
parametrization by this chamber cut.

Separately, some finite positive product cover `Fcover ⊆ D` exists:
`C0Plus * Fcover` remains dominant and covers all dominant valuation
values. Composing with the geometric coverage gives a `K₀` product
cover of `G(F)`. This assertion permits repeated valuation classes
and repeated double cosets.

For every full transversal with the additional chamber compatibility
`tildeC0Plus s F0 D = C0Plus B.S s Φ⁺ * F0`, the positive product is
itself a dominant section and its product pairs have distinct values.
Only with this additional condition does that product supply disjoint
representatives. No existence of a rectangular full transversal is
inferred from finite index or positivity alone.

## The same compact intersection in every standard Levi

The second conclusion is exactly
`SpecialCompactStandardLeviCompatibility B.apartment x ν s h j`,
where `h = B.centralizer.bijective`. For every
`J ⊆ simpleRelativeRoots B.i ν`, let
`M_J = Standard.leviScheme B.i ν J` and
`iM = Standard.leviTorusHom B.i ν J`. The compact subgroup is exactly
`KM = B.apartment.specialCompactLeviSubgroup ν J x`, the preimage of
the already fixed `K₀` under the actual Levi inclusion.
The published `specialCompactLeviSubgroup_map` identifies its ambient
image with `K₀ ⊓ standardLeviPoints B.i ν J`.

The statement concludes the existence of a closed actual factor
`jM : Z → M_J` representing the full centralizer of `iM`, with
`jM ≫ Standard.leviHom B.i ν J = j` and `s ≫ jM = iM`.
It concludes containment of the Levi positive roots in the ambient
positive roots and the exact `SameCompactLeviCartanComparison`.
Thus every actual Levi point has a dominant `jM(z)` representative
for `KM`, and the equality criterion on that Levi chamber is the same
`z′ z⁻¹ ∈ Z(F)^1`.

The concluded lattice predicate for `iM` uses the very same `Z`, `s`,
`ω_Z`, norm kernel, uniformizer group, full valuation lattice and
residue quotient. Only the root inequalities defining its chamber
change. The existing `sameCompactLeviChamberEquiv` and
`sameCompactLeviSectionEquiv` give the corresponding genuine
bijections with their actual representative formulas.
The root-containment lemmas compare the ambient and Levi dominant,
positive-uniformizer and chamber-cut sets. A full transversal may be
cut by each chamber; no simultaneous rectangular transversal is
required or asserted.

## Source correspondence and proof boundaries

The primary consumer source is David Renard, *Représentations des
groupes réductifs p-adiques*, registered 9 July 2026 edition,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.21–V.3.23, printed116–117/PDF122–123, defines the positive
chambers, full finite representatives and dominant intersection.
V.3.23 separately chooses the rectangular chamber compatibility.
V.5.1(4), printed122/PDF128, gives the disjoint Cartan representative
union; V.5.1(5) retains the same intersection `K₀ ∩ M` for every
standard Levi. The statement spells out which conclusions give a
disjoint section and which only give a finite positive cover.
The source's rectangular choice remains an explicit condition.

The geometric and positive-normalization source is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, read with the mandatory
1 November 2024 `kaletha-prasad-2024-corrections`. Theorem 4.2.15,
Theorem 5.2.1 and corrected (5.2.2), together with the corrections
PDF24–25 and 30, fix the compact stabilizer and the positive valuation
convention. The original parahoric theorem uses `P_x` and `Z(F)^0`.
The separate `AvailableCartanStatement` retains that indexing set.
This target concludes the additional comparison for `K₀` and `Z(F)^1`;
it does not identify these pairs of objects.

This packaging is derived: it requests the actual maximal-compact
geometric comparison, the existing lattice conclusions, and their
same-compact standard-Levi version under full local corrected
availability. The imported property definitions and their conditional
equivalences do not already prove these assertions for available data.
No Cartan coverage, classification, finite transversal or inherited
Levi comparison is a premise here.

General building existence, compact-open maximality, the other
special-compact properties of Renard V.5.1 and proofs of this target
remain separate obligations. No assignment or available datum is
asserted to exist by this conditional statement.
