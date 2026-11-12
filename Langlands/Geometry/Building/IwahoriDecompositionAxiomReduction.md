# KP Axiom 4.1.16 from the range part of KP Theorem 7.5.3(2)

`IwahoriDecompositionAxiomReductionStatement.{u}` is the implication from the
published `SimplyConnectedNormalizerAffineWeylStatement.{u}` to the published
`IwahoriDecompositionAxiomStatement.{u}`. The premise is the range part of KP
Theorem 7.5.3(2): `N(F) ∩ G(F)^♮` acts on the apartment through exactly
`W(Ψ)`. The conclusion is KP Axiom 4.1.16 (Iwahori decomposition) for the
building of supplied data. `iwahoriDecompositionAxiomReduction` proves this
implication.

The range statement remains an explicit premise. This unit does not prove
Axiom 4.1.16 without it. It shows that, once the range statement is proved,
nothing else is missing for Axiom 4.1.16. The range statement is used in only
one step: an element of `N(F) ∩ G(F)^0` that maps a chamber `C` onto itself
lies in `Z(F)^0`. All other steps use only published unconditional results.

## Statement

```lean
def IwahoriDecompositionAxiomReductionStatement : Prop :=
  SimplyConnectedNormalizerAffineWeylStatement.{u} → IwahoriDecompositionAxiomStatement.{u}
```

Both sides are the unchanged published Prop definitions at the same arbitrary
universe `u`:

- `SimplyConnectedNormalizerAffineWeylStatement` (module of the same name)
  quantifies over every nonarchimedean local field `F`, every group scheme `G`
  over `F` with `[IsAffineHom G.X.hom]` and every `P : ParahoricBuildingData G`
  with `P.apartment.SatisfiesApartmentAxioms P.centralizer`. It asserts that the
  image of `N(F) ∩ G(F)^♮` under `P.apartment.normalizerAffineEquiv` is
  `AffineRootSystem.affineWeylGroup P.affineRoots`.
- `IwahoriDecompositionAxiomStatement` quantifies over the same `F`, `G`, `P`
  with the single premise `P.SatisfiesApartmentAxioms` (by definition the same
  predicate) and concludes `P.HasIwahoriDecomposition`. That is the five
  fields of `IsIwahoriDecompositionAt C ν` for every chamber `C` of `A(S)` and
  every generic cocharacter `ν`: injectivity and range `I` of
  `(U(ν)(F) ∩ I) × Z(F)^0 × (U(-ν)(F) ∩ I) → G(F)`, where `I` is the
  stabilizer in `G(F)^0` of the image of `C`; existence of the least
  non-negative functionals `ψ_a`; and bijectivity of the ordered products of
  the `U_{ψ_a}` onto `U(±ν)(F) ∩ I` in every order without repetition.

No hypothesis is added on either side.

## The proof

The module proves the following declarations, in this order.

### Auxiliary lemmas

- `AffineRootSystem.IsAffineRootSystemWithRankZero.exists_parallel_root_pos`:
  for an affine root system `Ψ`, a point `p` and `ψ ∈ Ψ`, some `χ ∈ Ψ` has the
  same derivative as `ψ` and `χ p > 0`. By AR 4 (`infinite_fiber` and
  `finite_bounded_at`), some `θ ∈ Ψ` with derivative `ψ̇` has
  `|θ p| > 2|ψ p| + 1`. If `θ p > 0`, take `χ = θ`. Otherwise, by AR 2 for the
  coroot of `ψ` (`exists_isCoroot`), `θ - 2ψ ∈ Ψ`, and its negative
  `2ψ - θ ∈ Ψ` (`neg_mem`) has derivative `ψ̇` and is positive at `p`.
- `ofFn_prod_injective_range_congr` and `mul_mul_injective_range_congr`: two
  product maps built from equal families of subsets (or equal pairs of
  subgroups) have the same injectivity and the same range. They are used to
  move the published decompositions along equalities of factors.

### The functionals `ψ_a` and the factors `U_{ψ_a}`

- `ParahoricBuildingData.exists_isLeastNonnegativeFunctional`: under the
  apartment axioms, for every chamber `C` and every root `a` the least
  non-negative functional `ψ_a` on `C` exists. The derivative roots of
  `P.affineRoots` are the relative roots (`derivativeRoots_affineRoots`), so
  some affine root has derivative `a`. The lemma above gives an affine root `χ`
  with derivative `a` that is positive at the point `p` with `C` the facet of
  `p`, hence positive on `C` (`AffineRootSystem.mem_facet`). Then
  `ψ_a = χ - inf_C χ`. It is non-negative on `C`. Any affine functional `ψ'`
  with derivative `a` that is non-negative on `C` differs from `χ` by a
  constant (`apply_eq_apply_of_linear_eq_zero`), and this constant is at least
  `-inf_C χ`. Hence `ψ_a ≤ ψ'` pointwise.
- `ParahoricBuildingData.coe_affineRootGroup_eq_chamberRootBlock`: for `x ∈ C`,
  `U_{ψ_a}` is the depth-zero chamber root block `U_{a,x,0}` used by the
  published chamber decomposition. The chain is: `U_{a,C,0} = U_{a,x,0}` for the
  facet `C` (`rootFixer_eq_filtration_of_isFacet`, KP Lemma 6.3.20);
  `U_{a,C,0} = U_{ψ_a}` (`rootFixer_eq_affineRootGroup_of_isLeast`, whose
  minimality hypothesis follows from the leastness of `ψ_a` among all affine
  functionals); and the block equals the filtration group
  (`chamberRootBlock_eq_rootGroup`).

### The Iwahori subgroup as a stabilizer

- `ParahoricBuildingData.zeroStabilizer_le_parahoric`: suppose `x ∈ C`,
  `P_x ≤ P_C`, and every `n ∈ N(F) ∩ G(F)^0` (`P.normalizerZeroComponent`)
  with `n • C = C` lies in `Z(F)^0` (`P.normalizerZero`). Then the stabilizer
  `P.zeroStabilizer` of the image of `C` in `G(F)^0` lies in `P_C =
  P.parahoric C`. Proof: let `g` stabilize the image of `C`. Then
  `g • [x] = [y]` for some `y ∈ C`. By `ApartmentQuotient.mk_eq_mk_iff` there
  is `n ∈ N(F)` with `n • x = y` and `g⁻¹ n ∈ G(F)^♯_x`. Since
  `G(F)^♯_x ≤ P_x ≤ P_C` (`sharpFixer_le_parahoric`) and `P_x ≤ G(F)^0`
  (`parahoric_le_zeroSubgroup`), `n` lies in `G(F)^0`. The chamber `n • C`
  (`normalizer_smul_isChamber`) and `C` both contain `y`, so `n • C = C`
  (`IsFacet.eq_of_mem_mem`). By hypothesis `n ∈ Z(F)^0`, and `Z(F)^0 ≤ P_C`
  (`map_centralizerZero_le_parahoric`). Hence `g = n (g⁻¹ n)⁻¹ ∈ P_C`.
- `ParahoricBuildingData.mem_normalizerZero_of_iwahoriWeylChamberSplitting`:
  under `P.IwahoriWeylChamberSplitting C` (KP 7.8.2), the hypothesis of the
  previous lemma holds for `C`. The class of such an `n` in `W̃^0` lies both in
  `W_aff = P.affinePart` (as `n ∈ G(F)^0`) and in the chamber stabilizer
  `P.chamberStabilizer C`. These subgroups are complements, so they are
  disjoint, and the class is trivial, that is `n ∈ Z(F)^0`.

### Assembly

- `ParahoricBuildingData.isOrderedRootProductBijective_of_conclusion`: the
  ordered-product field for a cocharacter `κ`, given the published
  `ChamberIwahoriConclusion C x κ` and the equality
  `U(κ)(F) ∩ I = U(κ)(F) ∩ P_C`. Given an injective enumeration `a` of the
  non-divisible roots positive on `κ`, enumerate the negative ones
  (`Set.Finite.fin_param`, finiteness from `IsSplitTorus.finite_relativeRoots`)
  and apply the last clause of the conclusion at depth `0`. Its ordered product
  of the blocks `U_{a_j,x,0}` is injective with range `U(κ)(F) ∩ P_C`. By
  `coe_affineRootGroup_eq_chamberRootBlock` the factors are the `U_{ψ_{a_j}}`.
- `ParahoricBuildingData.isIwahoriDecompositionAt_of_forall_mem_normalizerZero`:
  `P.IsIwahoriDecompositionAt C ν` under the hypothesis on `N(F) ∩ G(F)^0`
  for `C`. Choose `x ∈ C`. The published unconditional
  `ParahoricBuildingData.chamberIwahoriDecomposition` (KP Corollary 7.4.9 with
  the `Z(F)^0` factor), applied to `ν` and to `-ν`, gives
  `ChamberIwahoriConclusion C x (±ν)`. Its first clause
  `P.chamberIwahori C = P.parahoricAt x` (where `chamberIwahori C` is
  `P.parahoric C`) gives `P_x ≤ P_C`, so `zeroStabilizer_le_parahoric`
  applies. The reverse inclusion `P_C ≤ I` passes through the pointwise fixer
  `P.zeroFixer C`: `parahoric_le_zeroFixer` followed by
  `zeroFixer_le_zeroStabilizer`. Hence `I = P_C`. Hence the unipotent factors
  agree, `U(±ν)(F) ∩ I = U(±ν)(F) ∩ P_C`. The injectivity and range of the
  triple product then come from the conclusion at `-ν`, whose negative factor
  is `U(ν)(F) ∩ P_C`. The functionals come from
  `exists_isLeastNonnegativeFunctional`, and the two ordered-product fields
  from `isOrderedRootProductBijective_of_conclusion` at `ν` and `-ν`.
- `ParahoricBuildingData.hasIwahoriDecomposition_of_iwahoriWeylChamberSplitting`
  and `iwahoriDecompositionAxiom_of_iwahoriWeylChamberSplitting`: KP 7.8.2 for
  every chamber (`IwahoriWeylChamberSplittingStatement`) implies
  `P.HasIwahoriDecomposition`, hence `IwahoriDecompositionAxiomStatement`.
- `iwahoriDecompositionAxiomReduction`: given the range statement `hW`, the
  published `iwahoriWeylNormalizerAffineWeylReduction hW` gives
  `IwahoriWeylChamberSplittingStatement` (its second component), and the
  previous theorem concludes.

## Provenance

The provenance is internal. The statement is an implication between two
published Prop definitions, and the proof composes published theorems. The
contextual source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (PDF page =
printed page + 31):

- Axiom 4.1.16, printed p.162 / PDF p.193 (the conclusion);
- Lemma 6.3.20, printed p.222 / PDF p.253 (`U_{a,x,0}` depends only on the
  facet of `x`);
- Corollary 7.4.9, printed p.257 / PDF p.288 (the decomposition of the chamber
  group, published as `chamberIwahoriDecomposition`);
- Lemma 7.5.2 and Theorem 7.5.3, printed pp.260–261 / PDF pp.291–292 (the
  premise is the range part of 7.5.3(2));
- Proposition 7.6.4(1), printed p.265 / PDF p.296 (`G(k)^0_C` is the
  stabilizer of `C` in `G(k)^0`);
- 7.8.2, printed p.273 / PDF p.304 (`W̃^0 = W_aff ⋊ W̃^0_C`).

The route differs from KP's. KP deduces Proposition 7.6.4(1) from the
Iwahori–Tits system (Theorem 7.5.3(1)) and Proposition 1.5.13. Here the
inclusion of the stabilizer in `P_C` is proved directly from the definition of
the building as a quotient, with KP 7.8.2 excluding nontrivial elements of
`W_aff` that stabilize `C`. The corrections
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF p.33)
add AS 5 to the Chapter 7 axioms. It is part of `SatisfiesApartmentAxioms` on
both sides, unchanged.
