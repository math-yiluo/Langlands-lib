# Renard VI.9.5 reduced to the generalized Jacquet lemma of VI.9.1

Author: Worker 76. Module
`Langlands.Representation.Families.RenardFamilyJacquetAdmissibilityReduction`,
namespace `Langlands.Renard.AlgebraicFamily`.

This module proves that the published VI.9.5 proposition
[`JacquetAdmissibleStatement`](RenardFamilyJacquetAdmissibilityStatement.md)
follows from the published VI.9.1 Theorem `GeneralizedJacquetLemmaStatement` of
[UniformCompressionStabilizationStatement](../Exponents/UniformCompressionStabilizationStatement.md).
The generalized Jacquet lemma stays an explicit premise. The module does **not**
prove `JacquetAdmissibleStatement` unconditionally. The other structural inputs
of the route, the comparison of an actual parabolic and Levi with dynamic ones,
are discharged by the published proofs `Langlands.GroupScheme.parabolicDynamic`
and `Langlands.GroupScheme.dynamicGeometricUnipotentRadical`.

## Declarations

| Declaration | Kind | Content |
| --- | --- | --- |
| `fixedJacquetMap_surjective_of_complexRepresentation` | theorem | For a family `ρ` over a `ℂ`-algebra `B`, surjectivity of `Jacquet.fixedJacquetMap` for the underlying complex representation `CoefficientRestriction.complexRepresentation ρ` gives surjectivity of `Jacquet.fixedJacquetMap ρ` over `B`, for the same subgroups |
| `fixedJacquetMap_surjective_congr` | theorem | Surjectivity of `Jacquet.fixedJacquetMap ρ N M hMN K` transfers along equalities `N' = N` and `M' = M`, with any normalizer proofs |
| `JacquetAdmissibleReductionStatement.{u', uB', uV'}` | `Prop`-valued definition | `GeneralizedJacquetLemmaStatement.{u', uV'} → JacquetAdmissibleStatement.{u', uB', uV'}` |
| `jacquetAdmissible_of_generalizedJacquetLemma` | theorem | Proves `JacquetAdmissibleReductionStatement` |
| `jacquetAdmissible_of_uniformCompressionStabilization` | theorem | `UniformCompressionStabilizationStatement.{u', uV'} → JacquetAdmissibleStatement.{u', uB', uV'}`, by composing the main theorem with the published `generalizedJacquetLemma_of_uniformCompressionStabilization` |

The VI.9.1 premise is used at the field universe `u'` of the target and at the
carrier universe `uV'` of the family `V`, because it is applied to the same
carrier `V` with complex scalars. The coefficient universe `uB'` stays free.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:

- VI.9.5, "Une autre conséquence", printed p. 201 / PDF p. 207: "Le foncteur de
  restriction `r_P^G : M(G, B) → M(M, B)` préserve la `B`-admissibilité.
  L'argument est le même que celle du corollaire VI.6.1." Worker 76 read this
  page;
- the Corollary of VI.6.1, printed pp. 176–177 / PDF pp. 182–183, whose argument
  is referred to;
- VI.9.1, the generalized Jacquet lemma, printed pp. 195–197 / PDF pp. 201–203.

The route below is the one the source indicates, with the surjectivity of
VI.9.1 in place of the finite-dimensional Jacquet lemma used in VI.6.1. The
module is derived by composition of published declarations. It asserts no new
external theorem, and the premise is a published statement.

## Proof of `jacquetAdmissible_of_generalizedJacquetLemma`

Fix the data of `JacquetAdmissibleStatement`: the field `k`, the connected
reductive `G`, the actual parabolic `p : P ⟶ G` with rational Levi `l`, radical
`r` and `hmul`, the coefficient ring `B`, a smooth family
`ρ : Representation B (rationalPoints G) V` whose compact-open fixed modules are
finitely generated over `B`, and a compact open subgroup `K'` of `M(k)`. Write
`N = pointImage (r ≫ p)` and `M_G = pointImage (l ≫ p)` for the literal radical
and Levi images in `G(k)`.

1. **Dynamic realization.**
   `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`, applied to the
   published proofs `parabolicDynamic` and `dynamicGeometricUnipotentRadical`,
   gives one cocharacter `χ` whose dynamic parabolic and centralizer are the
   ranges of `p` and `l ≫ p`. Then `pointImage_radical_eq_dynamic` gives
   `N = N(χ)(k)`, and the centralizer equality gives `M_G = M(χ)(k)`.
   The published `RationalPointFamily.dynamic_exists_central_hasOppositeIwahoriContractionBasis`
   gives a point `g` that commutes with every point of `M(χ)(k)` and an
   ambient-cofinal opposite contraction basis for `(N(χ), M(χ), N(χ⁻¹))` and `g`.

2. **Choice of `K`.** Let `e = leviPointsEquiv p l hp hl : M(k) ≃ₜ* M_G`, and let
   `ψ` be the character `jacquetCharacter` that normalizes the family Jacquet
   module. The open subgroup `L = e(K') ∩ ker ψ` of `M_G`, built as
   `K'.comap e.symm ⊓ ker ψ`, is the preimage of an open set `W` of `G(k)`
   containing `1`. The contraction basis gives a compact open `K ⊆ W` with
   `Jacquet.IsIwahoriContraction K N(χ) M(χ) N(χ⁻¹) g`. Then `K ∩ M_G ⊆ L`.

3. **Surjectivity.** Give `V` the complex structure through `algebraMap ℂ B`
   (`Module.compHom`), which forms a scalar tower with `B`. The premise, applied
   to `χ`, `K`, `g` and the smooth complex representation
   `CoefficientRestriction.complexRepresentation ρ`, says that its
   `Jacquet.fixedJacquetMap` for `(N(χ), M(χ))` is surjective. By
   `fixedJacquetMap_surjective_of_complexRepresentation` the same map for the
   family over `B` is surjective; by `fixedJacquetMap_surjective_congr` so is
   `Jacquet.fixedJacquetMap ρ N M_G _ K`.

4. **Finite generation.** Let `f : V^K → Jacquet ρ N` be the restriction of the
   quotient map `Jacquet.Localization.mk ρ N 1` to the `K`-fixed vectors. Its
   source is a finitely generated `B`-module by hypothesis. Let `x` be fixed by
   `K'` under `leviJacquetRepresentation`. For `m` in `K ∩ M_G`, `m ∈ L`, so
   `e⁻¹(m) ∈ K'` and `ψ(m) = 1`. Hence `x` is fixed by the unnormalized action
   of `K ∩ M_G` on the character-localized coinvariants. Through
   `Jacquet.Localization.trivialEquiv` it becomes a `K ∩ M_G`-fixed vector of the
   untwisted coinvariants `Jacquet.action ρ N M_G`. Step 3 gives `w ∈ V^K`
   mapping to it, and `f w = x` because `trivialEquiv` is injective. So the
   `K'`-fixed module is contained in the range of `f`. The range is finitely
   generated over the Noetherian ring `B`, hence a Noetherian module, so its
   submodule is finitely generated (`Module.Finite.of_injective`).

The hypothesis `Module.Flat B V` of the target is not used. Reducedness and
finite type of `B` over `ℂ` are not used either; only `IsNoetherianRing B`
enters, in step 4. The compactness of `K'` is not used: the argument applies to
every open subgroup of `M(k)`.

## Proof of `fixedJacquetMap_surjective_of_complexRepresentation`

Let `y` be a `K ∩ M`-fixed vector of the coinvariants of `ρ` over `B`, with
lift `v ∈ V`. The published `CoefficientRestriction.coinvariantsEquiv` identifies
the complex coinvariants of `complexRepresentation ρ` with those of `ρ`, as
quotients of `V` by relation submodules with the same elements
(`coefficientRelations_eq_native`: each `ρ(n)` is `B`-linear, so the `ℂ`-span of
the `ρ(n) v - v` is the `B`-span). It intertwines the two `M`-actions
(`coinvariantsEquiv_action`). So the complex class of `v` is `K ∩ M`-fixed, and
complex surjectivity gives a `K`-fixed `w` with the same complex class. The
`K`-fixed vectors of `ρ` and of `complexRepresentation ρ` are the same set,
and applying `coinvariantsEquiv` shows that `w` maps to `y` over `B`.

## The corollary from uniform stabilization

`jacquetAdmissible_of_uniformCompressionStabilization` composes the main theorem
with the published `RationalPointFamily.generalizedJacquetLemma_of_uniformCompressionStabilization`
of [GeneralizedJacquetReduction](../Exponents/GeneralizedJacquetReduction.md).

## Status of the premise

At Library commit `18a1f10aef8ea135d90e8474439a5e6d9c130008`, neither
`GeneralizedJacquetLemmaStatement` nor `UniformCompressionStabilizationStatement`
is proved. Their proof tasks are `cac6f709-2a1b-4eaa-a16d-63f2e40f3b29` and
`47e556e6-6b2a-40dc-ba66-d6a0585f5220`. Once either is published, applying the
corresponding theorem of this module to it proves `JacquetAdmissibleStatement`
for all universe levels. No admissibility over `ℂ`, finite length,
finite-dimensional fixed-vector, splitting or stabilization premise is added
beyond the named VI.9.1 statement.
