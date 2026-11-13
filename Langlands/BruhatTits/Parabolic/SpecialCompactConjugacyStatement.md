# Parabolic subgroups are conjugate to standard ones under `K₀` (Renard V.5.1, Corollary): statement

Module `Langlands.BruhatTits.Parabolic.SpecialCompactConjugacyStatement`. Namespace
`Langlands.BruhatTits`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`SpecialCompactParabolicConjugacyStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The V.5.1 Corollary has two assertions. The second,
compactness of `G/P`, is published and proved (`DynamicParabolicQuotientCompactStatement`,
proof `dynamicParabolicQuotientCompact`, and `ArbitraryParabolicQuotientCompactStatement`).
The proof note [QuotientCompactProof](QuotientCompactProof.md) says: "The K0-conjugacy
assertion of the same corollary is not proved here." No published statement states it. The
published `StandardParabolicClassificationStatement` gives conjugacy under `G(F)` only.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.5.1, printed pp.122–123 / PDF pp.128–129:

> Théorème. Il existe un sous-groupe compact maximal `K₀` de `G`, ouvert, tel que
> (1) `G = K₀ P_∅ = P_∅ K₀`. […]
>
> Un tel sous-groupe compact maximal `K₀` est dit adapté à `A_∅`.
>
> Corollaire. Si `P` est un sous-groupe parabolique quelconque de `G`, il est conjugué sous
> `K₀` à un sous-groupe parabolique standard. De plus `G/P` est compact.

## Published objects used

- `IsConnectedReductive`, `IsMaximalSplitTorus`, `IsGenericCocharacter`, `cocharacterLattice`,
  `characterLattice`, `simpleRelativeRoots`: the reductive-group framework of Chapter V.
- `standardParabolic i ν J` and its rational points `standardParabolicPoints i ν J`: the standard
  parabolic `P_J`; `J = ∅` gives the minimal parabolic `P_∅`.
- `Dynamic.parabolic zeta`: the parabolic subgroup `P(ζ)` of a cocharacter defined over `F`. As
  in `StandardParabolicClassificationStatement`, these are the parabolic subgroups of `G`
  defined over `F`.
- `G.innerIso k`: conjugation `x ↦ k x k⁻¹`, so `(P_J).comap (G.innerIso k).hom = k⁻¹ P_J k`.
- `Iwasawa.PointProductEqualities P K`: `G(F) = P K` and `G(F) = K P` as sets
  ([PointProducts](../Iwasawa/PointProducts.md)).

## The statement

**`SpecialCompactParabolicConjugacyStatement`.** Let `G` be a connected reductive group over a
field `F`, `S` a maximal split torus with a generic cocharacter `ν`, and `K` a subgroup of
`G(F)` with `G(F) = P_∅(F) K = K P_∅(F)`. Then for every cocharacter `ζ` there are a set `J`
of simple relative roots and `k ∈ K` with `P(ζ) = k⁻¹ P_J k`.

## Formalization choices

- **The hypothesis on `K₀`.** The Corollary uses only property (1) of the Theorem. The statement
  assumes exactly (1), as `PointProductEqualities (standardParabolicPoints i ν ∅) K`. A
  subgroup adapted to `A_∅` in Renard's sense satisfies it. The published
  `IwasawaExistenceStatement` asserts that the special compact subgroups of the building have
  this property for every parabolic.
- **The base field.** The argument uses no topology, so the statement is over an arbitrary
  field. The source's nonarchimedean local field is a special case.
- **Parabolic subgroups.** As in the published classification, a parabolic subgroup defined over
  `F` is `P(ζ)` for a cocharacter `ζ`, and conjugates are written with `comap` along the
  inner automorphism.

## Why the statement is true

By the published `StandardParabolicClassificationStatement`, `P(ζ) = g⁻¹ P_J g` for some
`g ∈ G(F)` and some `J`. By (1), `g = p k` with `p ∈ P_∅(F) ⊂ P_J(F)` and `k ∈ K`. Then
`g⁻¹ P_J g = k⁻¹ p⁻¹ P_J p k = k⁻¹ P_J k`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.BruhatTits.Iwasawa.PointProducts` | `PointProductEqualities`; through its imports `standardParabolicPoints`, `rationalPoints` |
| `Langlands.GroupScheme.Rational.StandardParabolicClassificationStatement` | `standardParabolic`, `simpleRelativeRoots`, `IsGenericCocharacter`, `Dynamic.parabolic`, `GroupScheme.innerIso` (through its imports), and the cited classification |
