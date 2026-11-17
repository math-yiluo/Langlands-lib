# Renard VI.10.7, Variant, last sentence, from the complex VI.7.5 Theorem

Module `Langlands.Representation.Families.RenardFamilyLeviInductionFiniteTypeReduction`,
namespace `Langlands.Renard.AlgebraicFamily`.

## Purpose and scope

The published statement `FamilyLeviInductionFiniteTypeStatement` (module
`RenardFamilyFiniteTypeStatements`) is the last sentence of the Variant in Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026
(registered as `renard-2026-representations-groupes-reductifs-padiques`), VI.10.7, Variant,
printed p.217 / PDF p.223: normalized parabolic induction `i_P^G` sends smooth
`(M(F), B)`-modules finitely generated over `B[M(F)]` to modules finitely generated over
`B[G(F)]`.

This module proves the implication

```
familyLeviInductionFiniteType_of_leviInductionFiniteType
  (H : LeviInductionFiniteTypeStatement.{u, uE}) :
  FamilyLeviInductionFiniteTypeStatement.{u, uB, uE}
```

from the published complex VI.7.5 Theorem `LeviInductionFiniteTypeStatement`
(module `Exponents/LeviInductionFiniteTypeStatement`). The complex statement is an explicit
premise. It is not proved here, so this module does not discharge the family statement. Once a
proof of `LeviInductionFiniteTypeStatement` is published, the family statement follows by
applying this theorem to it.

The complex statement is used at the universe pair `(u, uE)`: the field and the group points
live in `Type u`, and the complex representation it is applied to has its carrier in
`Type uE`, the universe of the family's carrier `E`. That carrier is a complex subspace of `E`.

The proof uses none of the hypotheses `Module.Flat B E`, `IsNoetherianRing B`,
`Algebra.FiniteType ℂ B` or `IsReduced B` of the family statement. The route is the third
proof route recorded in `RenardFamilyFiniteTypeStatements.md`. Renard's own text derives the
sentence from the `(G, B)`-version of the VI.10.7 Theorem and Proposition, which this module
does not use.

## Contents

### Generic part (any group, any `ℂ`-algebra `B`)

- `finite_asModule_of_complexSpan`. Let `ρ` be a `B`-linear representation of a group `H` on
  `V` and `π` a complex representation of `H` on `W`. Let `Φ : W →+ V` be an additive map with
  `Φ (c • w) = algebraMap ℂ B c • Φ w`, `Φ (π g w) = ρ g (Φ w)`, and image spanning `V` over
  `B`. If `W` is finitely generated over `ℂ[H]`, then `V` is finitely generated over `B[H]`.
  Proof: let `N` be the `B[H]`-span of the images of finitely many `ℂ[H]`-generators. The
  preimage of `N` under `Φ` is a complex subrepresentation containing the generators, so it is
  all of `W`. Hence `N` contains the image of `Φ`, and so also its `B`-span, which is `V`.
- `translateSpan ρ s`: the subrepresentation whose carrier is the span, over the coefficient
  ring, of all translates `ρ h x` with `x ∈ s`. `subset_translateSpan`: it contains `s`.
  `finite_translateSpan`: for a finite set `s` it is finitely generated over the group algebra.
  The elements of `s` are generators, because every translate of a generator lies in the
  subrepresentation they generate.
- `isSmooth_toRepresentation`: a subrepresentation of a smooth representation is smooth.
- `inducedComparison P τ τW incl hincl`. Here `P` is a subgroup of a topological group `G`,
  `τ` is a `B`-linear representation of `P` on `E`, where `E` also carries a compatible
  complex structure (`IsScalarTower ℂ B E`), `τW` is a complex representation of `P` on `W`,
  and `incl : W →ₗ[ℂ] E` is `P`-equivariant (`hincl`). Composition with `incl` is an additive
  map from the smooth induction of `τW` to that of `τ`, `f ↦ incl ∘ f`.
  `eval_inducedComparison` gives its values. `inducedComparison_smul`: it sends `c • f` to
  `algebraMap ℂ B c • (incl ∘ f)`. `inducedComparison_equivariant`: it commutes with right
  translation by `G`.
- `isSmooth_of_injective`: if `incl` is injective and `τ` is smooth, then `τW` is smooth.
- `mem_span_image_fixedVectors` (averaging). Assume `τ` and `τW` are smooth and the image of
  `incl` spans `E` over `B`. Let `H` be a compact open subgroup of `P`. Then every `H`-fixed
  vector of `E` lies in the `B`-span of the images of the `H`-fixed vectors of `W`. Proof:
  the published averaging projector `Compact.CharZero.averageMap` onto the `H`-fixed vectors
  commutes with `incl`, because both are equivariant (`averageMap_commute`). It also commutes
  with multiplication by every `b ∈ B`, because `τ` is `B`-linear. Write `v = ∑ bᵢ incl wᵢ`
  and apply the projector. A fixed vector is its own average (`averageMap_id`).
- `span_range_inducedComparison`. Now let `G` be locally compact and nonarchimedean, let `P`
  be closed with `P \ G` compact, and assume the hypotheses of the previous item. Then the
  image of `inducedComparison` spans the smooth induction of `τ` over `B`. Proof: let `f` be
  fixed by a compact open `K` (`exists_isCompact_fixedVectors`). Choose finitely many
  representatives `t` of the double cosets `P \ G / K`
  (`Induction.exists_finset_doubleCoset_representatives`). The value `f(i)` at a
  representative `i` is fixed by the compact open subgroup `conjOpenSubgroup P K i` of `P`
  (`Induction.eval_mem_fixedVectors`). By averaging, `f(i)` is a `B`-combination of vectors
  `incl w` with `w` fixed by the same subgroup. For each such `w`, the published section
  `Induction.fixedDoubleCosetSection` gives a `K`-fixed function of the induction of `τW`
  that is `w` at `i` and `0` at the other representatives. Its image under
  `inducedComparison` has the same property for `incl w`. A `B`-combination of these images
  is `K`-fixed and agrees with `f` at every representative, so it equals `f` by
  `Induction.fixedEvaluation_injective`.

### Represented parabolics

The section `Levi` works over a nonarchimedean local field `k`, for an affine group scheme
`G` whose rational points carry the canonical topology and are locally compact and
nonarchimedean.

- `finite_leviInducedRepresentation_of_complex`. Fix an actual rational parabolic
  `p : P ⟶ G` with rational Levi `l` and matching geometric unipotent radical `r`, and assume
  `P(F) \ G(F)` is compact. Assume `hcomplex`: the published complex induction
  `leviInductionFunctor p l r hp hr hl hmul` sends smooth complex representations of `M(F)`
  with carrier in `Type uE` that are finitely generated over `ℂ[M(F)]` to ones finitely
  generated over `ℂ[G(F)]`. Then, for every `ℂ`-algebra `B` and every smooth `B`-linear
  representation `σ` of `M(F)` on `E : Type uE` that is finitely generated over `B[M(F)]`,
  the family induction `leviInducedRepresentation p l r hp hr hl hmul σ` is finitely
  generated over `B[G(F)]`.

  Proof. Give `E` the complex structure `Module.compHom E (algebraMap ℂ B)`, so that
  `complexRepresentation σ` is `σ` viewed as a complex representation. Let `W` be
  `translateSpan` of the finitely many `B[M(F)]`-generators of `σ`: the complex span of their
  `M(F)`-translates. It is a smooth complex representation, finitely generated over
  `ℂ[M(F)]`, so `hcomplex` makes its induction finitely generated over `ℂ[G(F)]`. The image
  of `W` spans `E` over `B`: its `B`-span is `σ`-stable and contains the generators. On the
  parabolic image `pointImage p`, the inducing representation of the complex functor and that
  of the family induction have the same operators on `W ⊆ E`. The first uses the half-modulus
  on `P(F)`, and the second the half-modulus on the Levi composed with the projection
  `P(F) → M(F)`. They agree by the published `closedHalfCharacter_eq_comp_projection`, using
  the unimodularity `isUnimodularModulus_pointImage_radical` of the radical. So the inclusion
  `W → E` is equivariant, and `finite_asModule_of_complexSpan`, applied to
  `inducedComparison`, finishes the proof. Its spanning hypothesis is
  `span_range_inducedComparison`, which needs `P(F)` closed (`isClosed_pointImage`), the
  inducing representation smooth (`isSmooth_leviInducingRepresentation`) and compactness of
  `P(F) \ G(F)`.

- `familyLeviInductionFiniteType_of_leviInductionFiniteType`: the implication above.
  Compactness of `P(F) \ G(F)` for connected reductive `G` is the published
  `compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
  BruhatTits.dynamicParabolicQuotientCompact hG p hp`, as in the published proof
  `inductionBaseChange` of VI.8.2. The premise `hcomplex` is the complex statement `H`
  instantiated at the same field, group and parabolic.

## Notes

- `inducedComparison` is an additive map, not a `B`-linear one. The smooth induction of `τW`
  is only a complex space, and `inducedComparison_smul` records the compatibility with
  scalars.
- Axioms: the standard `propext`, `Classical.choice`, `Quot.sound`.
