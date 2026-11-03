# The chosen special vertex and its actual compact stabilizer

Worker 1229, task `219b673d-b7f3-47fb-9019-d1642687d4ac`.

This focused definition adapter fixes the subgroup and the quotient map used
by the special maximal compact targets. All declarations are in
`Langlands.Geometry.Building.KPApartmentData`.

## Sources and provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, with the
registered corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`.

The geometric predicates are those of Definition 1.3.39 and the facet/vertex
definitions in §1.3 (book PDF pages 60–61 for the special-point discussion).
The stabilizer is the actual `G(F)^1_x` of Axiom 4.1.2 and Theorem 4.2.15
(PDF pages 189 and 204–205). The quotient map is the restriction of the
published `N(F) → N(F)/Z(F)`. Its intended surjectivity at a special point
is the assertion used in the proof of Theorem 5.2.1 (PDF page 218), from
Lemma 1.3.42 and Axiom 4.1.6. Corrected AS 5 (corrections p.33) remains a prerequisite to that
assertion; this adapter does not establish it.

These are internal adapters on the published actual `KPApartment` and
`KPBuilding` objects, rather than new geometric constructions. The elementary
membership and inclusion lemmas follow from those definitions.

## Data and exact declarations

Let `F` be any nonarchimedean local field, with
`[Field F] [ValuativeRel F] [TopologicalSpace F]`
`[IsNonarchimedeanLocalField F]`. Both characteristics are included.
Let `i : S.toGrp ⟶ G` be a homomorphism over `F`, with
`[Mono i.hom.hom.left]` and `[IsAffineHom G.X.hom]`, and let
`D : KPApartmentData i (localFieldOrder F)`. The intended structural
specialization takes `G` connected reductive and `i` maximal split; those
hypotheses are not needed to form these definitions.

- `D.IsSpecialApartmentVertex x` is
  `AffineRootSystem.IsSpecialPoint D.affineRoots x ∧`
  `AffineRootSystem.IsVertex D.affineRoots x`. Both predicates concern the
  same point of the same actual reduced apartment. Specialness is geometric:
  every affine-root hyperplane has a parallel affine-root hyperplane through
  `x`. It is not defined by a desired subgroup property.
- `D.specialCompactSubgroup x` is exactly
  `D.compactStabilizer (D.apartmentMap x)`, hence
  `Plancherel.rationalCommonNormKernel G ⊓`
  `D.reducedFixer (D.apartmentMap x)`. This is the chosen `K₀` when
  `D.IsSpecialApartmentVertex x` holds. The definition also makes sense at
  other apartment points.
- `mem_specialCompactSubgroup` says that `g ∈ K₀` precisely when
  `g ∈ G(F)^1` and `g • D.apartmentMap x = D.apartmentMap x`.
  `specialCompactSubgroup_le_reducedFixer` and
  `specialCompactSubgroup_le_rationalCommonNormKernel` give the two inclusions.
- `D.specialCompactNormalizer x` is
  `(D.specialCompactSubgroup x).subgroupOf (normalizerPoints i)`. It is a
  subgroup of the actual `N(F)`, with membership described by
  `mem_specialCompactNormalizer`.
- `D.specialCompactWeylMap x` is the monoid homomorphism from that subgroup
  to the actual `relativeWeylGroup i = N(F)/Z(F)`, obtained by composing its
  inclusion into `N(F)` with the quotient homomorphism.
  `specialCompactWeylMap_apply` identifies its value with the actual coset
  of the normalizing point.

No origin in the apartment is chosen. The full reduced fixer and `K₀` remain
different definitions; no equality between them is asserted.

## Relation to Renard S19 and remaining targets

In the registered 9 July 2026 edition of Renard, V.5.1, printed page 122
(PDF page 128), and the public source map
`notes/renard/chapter-v-structural-inputs.md`, these definitions provide the
common chosen `K₀` and the actual quotient map for S19(2). Surjectivity is
not proved or stated as holding for every `KPApartmentData`.

S19(3) must use this same `D.specialCompactSubgroup x` for every standard
index `J`, and the literal pointwise product of the intersections with the
actual standard Levi and unipotent groups. S19(5) requires an actual
standard-Levi group-scheme adapter, its inherited apartment and its minimal
parabolic compatibility. Those statement targets are not part of this
definition unit. Iwasawa, Cartan and the smaller simultaneous basis remain
sibling targets.

`KPApartmentData` supplies only the split-torus part of V 6. Full corrected
validity, V 7 and the required building/apartment assertions are still
separate prerequisites. This module neither asserts compactness, openness
or maximality for every such `D`, nor supplies general existence of
corrected data and a special vertex. It introduces no parahoric or arbitrary
subgroup in place of the missing actual `P_x` and `G(F)^0`.
