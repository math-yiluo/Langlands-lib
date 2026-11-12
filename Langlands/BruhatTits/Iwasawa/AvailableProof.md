# KP Theorem 5.3.4 on available corrected Bruhat–Tits data

Author: Worker 102. Coauthor: Worker 3557, for the adapted compact-orbit
fixed-point argument described below.

`Langlands.BruhatTits.Iwasawa.availableIwasawa` has exactly the type
`Langlands.BruhatTits.Iwasawa.AvailableIwasawaStatement.{u}`, with arbitrary
universe `u`. It imports the published statement unchanged. For each field
and group its only building premise is `𝔅.IsAvailableFor F G hG`.
The proof uses `IsAvailableFor.groupAxioms` on that same datum. It does not
assert existence of an available assignment or of a special vertex.

For every special apartment vertex, the theorem gives both literal product
orders for the actual parahoric, its inclusion in the same compact
stabilizer, both orders for that stabilizer, and compact-open maximality.
It gives the same four conclusions for every special vertex of the reduced
building and every subgroup satisfying the actual `IsParahoricAt` relation.
The point-product families include all six families in `PointProducts`:
algebraic, dynamic and standard parabolics, and their rational conjugates.
All hypotheses and subgroup definitions are those of the published target.

## Special-point normalizer representatives

The proof imports
[the shared special-point Weyl representatives](../SpecialCompact/WeylRepresentatives.md).
The four helper arguments formerly here are preserved there, with
`SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective`
providing the representative used below. No Weyl-surjectivity premise is added.

## Chamber Iwasawa and all parabolics

`minimal_parahoric_products` chooses a regular facet whose closure contains
`x` using `exists_regularPoint_closure`. The chamber parahoric lies in the
point parahoric: monotonicity first passes to a chamber point, and
`sharpFixer_singleton_le_of_mem_facetClosure` passes to `x`.

The proof uses
`ParahoricBuildingData.iwasawaDecomposition_of_relativeTitsSystem`, the
published datum-level chamber theorem underlying `iwasawaDecomposition`,
with its algebraic premises discharged by `rootRankOneFactorization`,
`relativeTitsSystem` and
`hasSimpleRootParabolicFactorization_of_statements`. The latter is supplied
with the published `relativeRootSystem`, `standardParabolicEndpoints`,
`genericCentralizer` and `RelativeRoot.dynamicRootOrderedProduct`.
Thus the implementation needs no separate Henselian or perfect-residue
premise. It works with the existing chamber theorem's actual proof route.

Write a chamber decomposition as `u n p`. Choose a parahoric normalizer
representative `m` of the class of `n`. Then `n m⁻¹` is a centralizing point,
so `u (n m⁻¹)` belongs to the empty-index standard parabolic and `m p`
belongs to the point parahoric. This gives the first literal product
order. The internal `products_of_factorization` obtains the reverse order
by decomposing the inverse of each point and inverting the factors.

`family_of_minimal` uses `genericMinimalParabolic`,
`parabolicContainsMinimalStatement` and `minimalParabolicConjugacy` to
handle every actual algebraic parabolic. An elementary group argument
shows that if `H K` is the whole group, the same is true with any rational
conjugate of `H`: decompose the conjugating element in `K H` and absorb
its `H` component. The dynamic family follows from
`Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic` with
the published `parabolicDynamic`, and its exact represented point range.
`standardParabolicOrder` places the empty-index standard parabolic in
every valid `P_J`. The conjugate families use
`rationalPoints_range_comp_innerIso` and
`standardParabolicPoints_comap_innerIso_inv`; dynamic conjugates are
already included among all dynamic cocharacters.

The same elementary conjugation argument, followed by mapping both
factors, proves the corresponding result for every conjugate of `K`.
The internal `family_conjugate` and `family_mono` apply these arguments to
each of the six families and preserve the fixed subgroup across them.

## The compact stabilizer

`ParahoricBuildingData.parahoricAt_le_compactStabilizer`, with the topology
compatibility projected from the apartment axioms, proves the apartment
inclusion. Its whole-building version follows by conjugation using
`conj_mem_compactStabilizer`. Enlarging the parahoric factor gives all
product conclusions for the same compact stabilizer.

For compactness, the available `HasBoundedOpenStabilizers` axiom gives an
open algebraically bounded stabilizer. An open subgroup is closed, and
`IsAlgebraicallyBounded.isCompact_closure` makes it compact in the
canonical rational-point topology.

For maximality, `metricRealization` supplies a complete nonpositively
curved realization of the existing reduced building from the available
axioms. The internal `compact_subgroup_fixes` adapts the orbit-isometry
argument of Worker 3557's public draft for Task 5270
(`a20a7c6a-18e6-430e-9ebd-f4e7046e075d`, draft revision 1).
The needed argument is implemented and checked in this file: a compact
subgroup has a compact, hence bounded, orbit by continuous orbit maps;
`completeNPCGeodesic` and `boundedSetStabilizerFixedPoint` give its common
fixed point. The subgroup preserves its orbit because it is closed under
products and inverses.

If a compact subgroup contains the special point's norm-one stabilizer,
its fixed point is fixed by that stabilizer.
`eq_of_compactStabilizer_fixed_of_special_buildingPoint` identifies the
point with the given special point, using the available apartment
injection and the common apartments supplied by
`hasCommonApartmentWith_of_isBuilding`. Finally,
`compactSubgroup_le_rationalCommonNormKernel` places the overgroup in the
actual rational-character norm kernel. It therefore lies in the same
compact stabilizer. This proves maximality among all compact subgroups.
The public bounded-subgroup fixed-point target is not assumed or imported
as a proof.

## Whole-building charts and the exact target

For a parahoric chart `y = g • apartmentMap x`, the quotient-coordinate
lemma `exists_normalizer_eq_on_translated_facetClosure` compares it with
any chart exhibiting specialness of `y`. It supplies a normalizer sending
that special apartment point to `x`. Its affine-root-preserving action,
from the apartment axioms, transfers specialness by
`isSpecialPoint_apply_iff`. The apartment product result can consequently
be conjugated to the actual specified parahoric `Q`. The compact argument
applies directly at `y`.

`available_point_conclusions` assembles these four conclusions without
requiring an extra chart certificate. The final theorem specializes it at
each apartment point and at each whole-building parahoric. The vertex
premises remain exactly those of the target, although the internal
arguments only require specialness. Neither `AvailableCartanStatement`
nor `ParahoricLeCompactStabilizer` is used as a hypothesis.

## Sources and verification

The source theorem is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Theorem 5.3.4, printed pp.190–191 / PDF pp.221–222. The chamber
input is Theorem 5.3.3. The compact-stabilizer conclusion follows the
fixed-point route of Theorem 4.2.15(1), printed pp.173–174 / PDF
pp.204–205, specialized here to special points and local-field compactness.
Registered source: `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The mandatory 1 November 2024 *Corrections and additions* supplies the
corrected Definition 4.1.26 on PDF p.27 and the corrected neighboring
chamber proof on PDF p.30. The statement of 5.3.4 is unchanged. Registered
source: `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The helper arguments are internal derivations from the named Library
results. The proof has no holes or new axioms. Local Lake compilation and
declaration inspection succeed with universe parameter `u` and axioms
`propext`, `Classical.choice`, and `Quot.sound`. Independent review and
exact-target publication validation remain required.
