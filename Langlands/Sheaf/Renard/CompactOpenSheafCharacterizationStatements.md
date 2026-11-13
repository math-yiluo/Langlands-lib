# Sheaves on a t.d. space as unions of compactly supported sections (Renard II.2.4): statements

Module `Langlands.Sheaf.Renard.CompactOpenSheafCharacterizationStatements`.
Namespace `Langlands.Sheaf.Renard`. Universe parameters `u` (the space) and `v` (section
groups).
The module contains three **statements**, the `Prop`-valued definitions
`CompactOpenSheafCharacterizationStatement`, `LocallyConstantCompactSectionsStatement` and
`PointwiseTestAlgebraUnitalIffCompactStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The II.2.4 Proposition had no published statement.
The published [GermSupport](GermSupport.md) and
[GermSupportClosednessStatement](GermSupportClosednessStatement.md) leave the
"II.2.4 compact-open exhaustion" as a separate unit. [ClopenExtension](../ClopenExtension.md)
constructs the clopen zero extension as an internal prerequisite and claims no comparison
with the source proposition.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read II.2.4, printed p.38 / PDF p.44:

> Proposition. Soit `X` un espace t.d. et soit `F` un faisceau (de groupes abéliens) de base
> `T_c`. Alors il existe un groupe abélien `F_c(X)` et un faisceau `F₁` isomorphe à `F` tels
> que
> 1. pour tout `U ∈ T_c`, `F₁(U) ⊂ F_c(X)`,
> 2. si `U ⊂ V` sont des ouverts de `T_c`, alors `F₁(U) ⊂ F₁(V)`,
> 3. si `U ⊂ V` sont des ouverts de `T_c`, alors pour tout `f ∈ F₁(U)`, `ρ_{V,U}(f) = f`
>    tandis que `ρ_{V,V∖U}(f) = 0`,
> 4. `F_c(X) = ⋃_{U ∈ T_c} F₁(U)`.
>
> Exemple. Soit `𝒞^∞_X` le faisceau dont l'espace des sections au-dessus d'un ouvert `U` est
> l'espace `𝒞^∞(U)` des fonctions localement constantes sur `U`. Le groupe abélien donné par
> la proposition est dans ce cas `𝒟(X)`, l'espace des fonctions localement constantes à
> support compact sur `X`. […] Remarquons aussi que l'algèbre `𝒟(X)` n'est en général pas
> unitaire, sauf si `X` est compact, auquel cas `𝒞^∞(X) = 𝒟(X)`, dont l'unité est `χ_X`.
> En revanche, c'est une algèbre à idempotents […].

`T_c` is the set of compact open subsets of `X`.

## Published objects used

- `ProjectorBasisSheaf.compactOpenBasis hX : OpenBasis X`: the compact opens of a t.d. space
  (`hX : Langlands.Topology.IsLocallyProfinite X`), Renard's `T_c`.
- `BasisSheaf B`: Renard's sheaves of abelian groups of base `B` (normalized presheaves on the
  basis satisfying the sheaf condition (F) of II.2.1), with `Sections F.obj.obj U` and the
  restriction maps `restriction F.obj.obj h` ([BasisSheaf](BasisSheaf.md),
  [BasisPresheaf](BasisPresheaf.md)).
- `LocallyConstantScalar.basisSheaf B ℂ`: the sheaf `𝒞^∞_X` on the basis `B`, with
  `Sections = LocallyConstant U ℂ` ([LocallyConstantScalarSheaf](LocallyConstantScalarSheaf.md)).
- `HarmonicAnalysis.PointwiseTestAlgebra.Carrier X`: the algebra `𝒟(X)` of compactly supported
  locally constant complex functions with pointwise operations
  ([PointwiseTestAlgebra](../../HarmonicAnalysis/PointwiseTestAlgebra.md)).

## The statements

**`CompactOpenSheafCharacterizationStatement`** (the Proposition). For every t.d. space `X`
and every sheaf `F` of base `T_c` there exist an abelian group `F_c` (in `Type (max u v)`),
subgroups `S U ⊂ F_c` for `U ∈ T_c`, and additive isomorphisms `φ_U : F(U) ≃ S U` such that:

- (2) `S U ⊂ S V` whenever `U ⊂ V`;
- (4) every element of `F_c` lies in some `S U`;
- (3, first half) for `U ⊂ V` and `y ∈ S U`, restricting `φ_V⁻¹(y)` to `U` and applying `φ_U`
  gives back `y`;
- (3, second half) for `U ⊂ V`, `W = V ∖ U` and `y ∈ S U`, the restriction of `φ_V⁻¹(y)`
  to `W` is `0`.

**`LocallyConstantCompactSectionsStatement`** (the Example). For `F = 𝒞^∞_X` the data can be
taken with `F_c = 𝒟(X)`, `S U` the functions in `𝒟(X)` supported in `U`, and
`φ_U(s)(x) = s(x)` for `x ∈ U` (the extension by zero), and they satisfy (2)–(4).

**`PointwiseTestAlgebraUnitalIffCompactStatement`** (the Example). `𝒟(X)` has a unit if and
only if `X` is compact.

## Formalization choices

- **The sheaf `F₁`.** Renard asks for a sheaf `F₁` isomorphic to `F` with `F₁(U) ⊂ F_c(X)`.
  The statement gives the subgroups `S U = F₁(U)` and the isomorphisms `φ_U : F(U) ≃ F₁(U)`.
  The restriction maps of `F₁` are those of `F` transported by the `φ_U`. With them `F₁` is a
  sheaf and `φ` is an isomorphism of sheaves, by construction. Item 1 is the fact that the
  `S U` are subgroups of `F_c`. Item 3 is stated for the transported restrictions.
- **`V ∖ U`.** For compact opens `U ⊂ V` of a Hausdorff space, `V ∖ U` is again compact open.
  The statement quantifies over a basis open `W` with `W = V ∖ U` as sets and `W ⊂ V`, rather
  than constructing `V ∖ U` inside the statement.
- **Universe of `F_c`.** The source's `F_c(X)` is the group of compactly supported sections of
  the étalé space, whose stalks are direct limits over neighbourhoods. It is taken in
  `Type (max u v)`, the universe of these stalks.
- **The Example.** "Le groupe abélien donné par la proposition est dans ce cas `𝒟(X)`" is
  stated as the existence of data for the Proposition with `F_c = 𝒟(X)`, functions supported
  in `U` and extension by zero. "N'est en général pas unitaire, sauf si `X` est compact" is
  stated as an equivalence. That `𝒟(X)` is an algebra with idempotents is the published
  `PointwiseTestAlgebra.isIdempotented` and is not restated.

## Why the statements are true

- **The Proposition** follows Renard's proof. `F` is isomorphic to the sheaf `F⁺` of continuous
  sections of its étalé space (II.2.1; the published `RenardSheafGermUnitIsoStatement` is
  proved). Let `F_c` be the compactly supported global sections of `F⁺` and `S U` those
  supported in `U`. For compact open `U`, the set `X ∖ U` is open, so extending a section over
  `U` by `0` gives a global section supported in `U`. This defines `φ_U`. Items 2 and 3 are
  immediate. For item 4, the support of an element of `F_c` is compact by definition (and
  closed, II.2.2). It is covered by finitely many compact opens, whose union is a compact
  open.
- **The Example.** For `𝒞^∞_X`, extending a locally constant function on the clopen `U` by zero
  gives a locally constant function with compact support in `U`. Every element of `𝒟(X)` arises
  this way from its compact support. If `X` is compact, the constant function `1` lies in
  `𝒟(X)` and is a unit. Conversely, let `e` be a unit. For each `x` choose a compact open
  `U ∋ x`. Then `e χ_U = χ_U`, so `e(x) = 1`. Hence the support of `e`, which is compact, is
  all of `X`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Sheaf.Renard.ProjectorPresheaf` | `ProjectorBasisSheaf.compactOpenBasis`; through its imports `BasisSheaf`, `Sections`, `restriction` |
| `Langlands.Sheaf.Renard.LocallyConstantScalarSheaf` | `LocallyConstantScalar.basisSheaf` |
| `Langlands.HarmonicAnalysis.PointwiseTestAlgebra` | `PointwiseTestAlgebra.Carrier` |
