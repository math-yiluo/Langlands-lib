# The chosen minimal parabolic in the actual standard Levi

This pair states the algebraic minimal-parabolic compatibility needed for the
standard-Levi clause in Renard S19(5). Its global declaration is
`Langlands.GroupScheme.StandardLeviMinimalParabolicCompatibilityStatement`.
The declaration is a proposition definition; this pair does not prove it.

## Source and derived content

The registered source is Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 edition,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
In V.5.1(5), printed page 122 / PDF page 128, the minimal parabolic in each
standard Levi `M` is the intersection of the chosen ambient minimal parabolic
with `M`. The original passage is about rational-point groups.

The all-test formulation is a derived scheme-level refinement. It uses the
published actual closed `Standard.leviScheme` and `Standard.leviHom`, the
same-torus factor `Standard.leviTorusHom`, the dynamic subgroup functor defined
by orbit extensions, and `IsMinimalParabolicFunctor`. In that predicate,
parabolicity requires representation by an actual parabolic subgroup over the
ground field, and minimality compares all rational parabolic subgroup functors
by inclusion on every test scheme. Minimality is not inferred from the group
of rational points.

The proved comparison adapters are internal consequences of
`Dynamic.parabolic_eq_comap_of_isClosedSubgroup`,
`Dynamic.range_inf_parabolic`, `Standard.leviTorusHom_comp`, and
`Standard.isRepresentedBy_leviHom`. The source passage alone is not claimed
as a proof of the scheme-level target.

## Actual objects and proved comparisons

Fix a field `F`, an affine group scheme `G/F`, a commutative group scheme `S/F`,
a homomorphism `i : S → G`, a cocharacter `ν` of `S`, and an index set `J`.
These inputs need no building, maximal-split, genericity or standard-index
assumptions for the comparison lemmas.

Write `L = Standard.leviScheme i ν J`,
`j = Standard.leviHom i ν J`, and
`iL = Standard.leviTorusHom i ν J`. The torus map has `iL ≫ j = i`.
`Standard.leviGenericParabolic i ν J` is precisely the intrinsic dynamic
parabolic of the cocharacter `ν ≫ iL` in `L`. Its name does not assert its
minimality without the structural hypotheses.

`Standard.leviGenericParabolic_eq_comap_dynamic` proves

```text
P_L(ν ≫ iL) = j⁻¹ P_G(ν ≫ i).
```

The proof applies the existing closed-subgroup comparison to the actual `j`
and simplifies the cocharacter composite using `iL ≫ j = i`. Equality is of
subgroup functors on every test scheme, including nonaffine and nonreduced
tests.

`Standard.leviGenericParabolic_eq_comap_standard` replaces the ambient dynamic
parabolic by `standardParabolic i ν ∅` under the explicit endpoint equality
between those two functors. This endpoint is a conclusion of the existing
`StandardParabolicEndpointsStatement`, not an unconditional fact assumed here.

`Standard.leviGenericParabolic_points_map` assumes the same endpoint equality
and proves the literal subgroup identity inside the actual `G(F)`:

```text
j(P_L(ν ≫ iL)(F)) = P_∅(F) ∩ M_J(F).
```

The proof specializes `Dynamic.range_inf_parabolic` to the identity test scheme,
uses the actual represented range of `j` to identify `M_J(F)`, and commutes
the two intersection factors. Its map is `rationalPoints.map j`.

## Structural target and hypotheses

`Standard.LeviMinimalParabolicCompatible i ν J` is the conjunction of:

1. Connected reductivity of the actual `L`.
2. Minimal parabolicity of the chosen ambient `standardParabolic i ν ∅`.
3. Minimal parabolicity of the intrinsic `P_L(ν ≫ iL)`.
4. Equality of that intrinsic functor with the pullback of the same chosen
   ambient minimal parabolic.
5. The displayed literal rational-point image intersection.

The global `StandardLeviMinimalParabolicCompatibilityStatement` asks for this
conjunction for every full nonarchimedean local field `F`, every actual
connected reductive `G/F`, every chosen maximal split torus `i`, every generic
cocharacter `ν`, and every `J ⊆ simpleRelativeRoots i ν`. There is no
restriction on the characteristic, splitting field or ramification. The
affine instance comes from the ambient connected-reductive hypothesis.
The same `i` and `ν` are used for all `J`; the target does not select a new
torus or a replacement Levi.

## Connection with the chosen compact subgroup

`KPApartmentData.specialCompactLeviSubgroup` in the prerequisite
`SpecialCompactLevi` pair is already the preimage of the same chosen
`KPApartmentData.specialCompactSubgroup x` along the actual `j(F)`. Its ambient
image is the literal `K₀ ∩ M_J(F)`. The present pair specifies which minimal
parabolic in this same Levi belongs to Renard S19(5).

This pair supplies only that algebraic part of S19(5). The geometric inherited
apartment, corrected root-valuation data, compactness, openness, maximality,
Weyl representatives and the S19(3) compact-parabolic product remain separate
obligations. The Iwasawa and Cartan conclusions in S19(1),(4) are sibling
targets. No conclusion about an arbitrary weak `KPApartmentData` is made, and
no general existence target is replaced by this algebraic statement.
