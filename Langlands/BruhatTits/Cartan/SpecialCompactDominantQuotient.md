# Dominant representatives for the chosen geometric compact stabilizer

This internal definition unit constructs the dominant representative map for
the shared geometric subgroup `K₀`, the equivalence relation it induces, and
the resulting injective quotient map. It does not assert a Cartan
decomposition or classify this relation by a valuation kernel.

## Actual objects and scope

The field `F` is any nonarchimedean local field with the existing
`Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. Both characteristics are allowed.
The inputs are actual group schemes `G` and `Z`, a commutative group scheme
`S`, and group-scheme maps `i : S → G`, `j : Z → G` and `s : S → Z`.
The map `i` has the published monomorphism instance and `G` is affine.
The comparison `h : Bijective (restrictionEvaluation s)` is explicit.

Take `D : KPApartmentData i (localFieldOrder F)` and `x : D.Apartment`.
Every occurrence of `K₀` in this file means exactly

`D.compactStabilizer (D.apartmentMap x)`

or, on expanding the published definition,

`Plancherel.rationalCommonNormKernel G ⊓ D.reducedFixer (D.apartmentMap x)`.

There is no independently chosen subgroup parameter. This is also the
expression fixed by Worker 1229's special-compact adapter. The definitions
here use the already published expression directly.

In the intended actual-centralizer specialization, `G` is connected reductive,
`i` is maximal split, `j` is a closed embedding representing
`torusCentralizer i`, and `s ≫ j = i`. The point `x` must be both special and
a vertex for `D.affineRoots`. These hypotheses are not needed to form the
maps in this unit and are not inferred from its inputs. In particular,
`KPApartmentData` alone does not supply the full corrected building axioms,
general existence, or compactness and maximality of this stabilizer.

The set `Zdom` is the existing `dominantCentralizer i ν s h`. It consists of
actual points `z ∈ Z(F)` satisfying

`0 ≤ eval S a (centralizerValuation s h z).toAdd`

for all `a ∈ positiveRelativeRoots i ν`. This retains the corrected positive
character-valuation convention. The definitions make sense for every `ν`;
the intended chamber specialization additionally requires the actual
generic cocharacter selecting a minimal parabolic.

## The induced relation and quotient

`dominantCompactRepresentative D x ν j s h` sends `z ∈ Zdom` to the double
coset of the actual point `rationalPoints.map j z.val` in
`K₀ \ G(F) / K₀`. Its domain and codomain are the existing rational-point
objects, with no abstract replacement of the group.

`dominantCompactSetoid` is the kernel equivalence relation of this function.
The theorem `dominantCompactSetoid_iff` expands it as

`z ~ z' ↔ ∃ k ∈ K₀, ∃ k' ∈ K₀, j(z') = k * j(z) * k'`.

The proof applies Mathlib's double-coset equality criterion. This is the
literal induced relation, not an assertion identifying it with a simpler
centralizer relation.

`DominantCompactQuotient` is the set quotient by this relation and
`dominantCompactClass` is its class map.
`dominantCompactClass_eq_iff` identifies equality of classes with equality of
their image double cosets. `dominantCompactDoubleCosetMap` is the quotient
lift of the representative map, with well-definedness built from exactly
the defining relation. Its representative law is
`dominantCompactDoubleCosetMap_class`.

The map is injective by `dominantCompactDoubleCosetMap_injective`: the kernel
quotient universal property makes equal image values equivalent
representatives. This elementary injectivity result does not prove the
source-facing classification of the relation.

`dominantCompactDoubleCosetMap_surjective_iff` identifies surjectivity with
the explicit requirement that every actual group point's double coset has
a dominant representative. Its proof descends to representatives of both
quotients. `dominantCompactDoubleCosetEquiv` packages the genuine bijection
only after this coverage proof is supplied; its representative formula is
`dominantCompactDoubleCosetEquiv_class`. No universal coverage statement
about the available apartment data occurs in this file.

## The two source-facing indexing sets remain separate

The existing `DominantNormQuotient i ν s h` uses the restricted right-coset
relation `z' * z⁻¹ ∈ rationalCommonNormKernel Z`, namely `Z(F)^1` for an
actual centralizer. It already bijects with `dominantValuationImage i ν s h`,
the chamber in the actual valuation image. This file does not identify
that relation with `dominantCompactSetoid`. Such an identification, as well
as actual dominant coverage, remains an explicit geometric comparison
obligation before the valuation chamber can parametrize these `K₀` double
cosets. No identification with the full integral cocharacter lattice is
asserted.

The KP parahoric indexing set instead uses `Z(F)^0` and the actual `P_x`.
Neither object is defined here, and no equality of `P_x` and `K₀` or of
`Z(F)^0` and `Z(F)^1` is asserted. The corrected parahoric equality criterion
and its quotient bijection remain separate targets. Renard's actual
`C₀⁺`, finite `F₀`, representative set `tilde C₀⁺` and standard-Levi
comparisons must use this same `K₀`. A product covering by finite translates
need not be a disjoint representative parametrization; this construction
does not supply either comparison.

## Provenance

The construction is internal: it specializes the kernel quotient universal
property to the published actual dominant set, rational-point map,
apartment map and compact stabilizer. The quotient and injectivity use
Mathlib's `Setoid.ker` and `Setoid.kerLift`. The coverage equivalence uses
quotient induction, and the final equivalence packages that surjectivity
with the already proved injectivity. These are elementary construction
laws rather than proofs of a Cartan statement.

The source-facing motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Theorem 5.2.1 and equation (5.2.2), printed pages 186–188 (PDF 217–219).
The geometric stabilizer is the published `G(F)^1_x` used in Theorem
4.2.15, printed pages 173–174 (PDF 204–205). The mandatory 1 November
2024 corrections, `kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pages 24–25 and 30, fix the positive valuation convention and the
nonnegative chamber.

Renard's registered 9 July 2026 edition,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
V.3.23, printed page 117 (PDF 123), and V.5.1(4)–(5), printed page 122
(PDF 128), motivate the separate maximal-compact and finite-representative
comparisons. These references explain the intended later specialization;
they are not claims that the sources establish Cartan assertions for
arbitrary inputs of this unit.
