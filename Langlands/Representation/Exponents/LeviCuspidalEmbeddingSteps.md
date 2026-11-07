# Unconditional steps towards Renard VI.2.1 for actual represented parabolics

Module `Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps`.

## Purpose and scope

Renard, *Représentations des groupes réductifs p-adiques* (2026 version), VI.2.1,
Corollary and proof (printed p. 139 / PDF p. 145), argues in four steps. Let `π` be an
irreducible smooth representation of `G`.

1. Choose a parabolic `P = MN` that is minimal among those with `r_P^G(π) ≠ 0`. Such
   parabolics exist because `r_G^G(π) = π ≠ 0`.
2. Transitivity of Jacquet functors (VI.1.4, with V.3.11) and minimality show that
   `r_P^G(π)` is supercuspidal.
3. Finite generation (VI.1.3) gives an irreducible quotient `τ` of `r_P^G(π)`. By
   exactness, `τ` is supercuspidal.
4. Frobenius reciprocity turns the nonzero quotient map `r_P^G(π) → τ` into a nonzero, and
   hence injective, map `π → i_P^G(τ)`.

This module proves the parts of steps 1, 3 and 4 that need no represented transitivity,
no parabolic extension and no finite-type theorem. For actual parabolics, step 2 needs
an extension result and transitivity. Step 3 needs the finite-type theorem. Those inputs
are the separate propositions `LeviParabolicExtensionStatement`,
`LeviParabolicTransitivityStatement` and `LeviJacquetFiniteTypeStatement`, and this module
does not use them. The module proves no form of the target
`LeviCuspidalEmbeddingStatement`. It supplies the pieces that an assembly will combine
with those inputs.

In contrast with the source, the parabolics are arbitrary actual rational parabolics of
the group scheme `G`, not standard ones. Minimality is measured by the all-test range
`SubgroupFunctor.range p` of the inclusion `p : P ⟶ G`, not by inclusion of standard
parabolics.

## Declarations

### Closed subgroups (namespace `Langlands.GroupScheme.IsClosedSubgroup`)

Here `k` is a field and all group schemes are over `Spec k`.

- `isIso_of_range_le_range_comp`: let `q : Q ⟶ M` and `j : M ⟶ G` be closed subgroups
  (`IsClosedSubgroup`). If `SubgroupFunctor.range j ≤ SubgroupFunctor.range (q ≫ j)`,
  then `q` is an isomorphism. The descent step will use this to show that a parabolic
  of the Levi with the full range is not proper.
- `ker_ideal_lt_of_range_lt`: let `G` be affine, and let `i : H ⟶ G` and `i' : H' ⟶ G` be
  closed subgroups with `range i < range i'`. Then the kernel ideal of `i'` on the top
  affine open of `G` is strictly smaller than the kernel ideal of `i`.

### Parabolic data (namespace `Langlands.Aubert.General.RepresentedParabolic`)

- `ParabolicDatum G`: a structure that bundles the data quantified in
  `LeviCuspidalEmbeddingStatement`:
  - group schemes `P`, `M` and `U` over `Spec k`;
  - morphisms `p : P ⟶ G`, `l : M ⟶ P` and `r : U ⟶ P`;
  - proofs `hp : IsParabolicSubgroup p`, `hl : IsRationalLeviSubgroup l`,
    `hr : LeviSubgroup.IsGeometricUnipotentRadical r` and
    `hmul : IsIso (subgroupMultiplication l r)`.

  It is internal packaging with no new mathematical content. Bundling the data lets
  them be compared by `SubgroupFunctor.range p`.
- `ParabolicDatum.identity hG`: the datum for a connected reductive `G` with `P = M = G`,
  `p = l = 𝟙 G`, `U` the trivial group and `r = kernelUnit G`. Its four proofs are the
  published `IsConnectedReductive.isParabolicSubgroup_id`, `isRationalLeviSubgroup_id`,
  `isGeometricUnipotentRadical_kernelUnit` and
  `isIso_subgroupMultiplication_id_kernelUnit` (module
  `Langlands.GroupScheme.Rational.IdentityParabolic`).
- `ParabolicDatum.exists_minimal`: let `G.X.hom` be affine and locally of finite type,
  and let `S` be a predicate on parabolic data. If some datum satisfies `S`, then some
  datum `D` satisfies `S` and has the following minimality property: no datum `D'`
  satisfying `S` has `range D'.p < range D.p`.

### Jacquet modules

- `normalizedJacquetFunctor_map_surjective`: for a locally compact nonarchimedean group
  `H`, a closed subgroup `N` and a subgroup `L` normalizing `N`, the normalized Jacquet
  functor `normalizedJacquetFunctor N L` sends every intertwiner with surjective
  underlying map to an intertwiner with surjective underlying map.
- `exists_minimal_nontrivial_leviJacquet`: the hypotheses are those of the target
  statement for `k`, `G` and the topology on `G(k)`: `k` is a nonarchimedean local
  field, `G` is connected reductive, `G(k)` has the canonical point topology and is
  locally compact and a nonarchimedean group. For every nontrivial
  `π : SmoothRep.{0, u, v} ℂ G(k)` the conclusion has two parts:
  - there is a datum `D` whose normalized Levi-valued Jacquet module
    `(leviJacquetFunctor D.p D.l D.r D.hp D.hr D.hl D.hmul).obj π` is nontrivial;
  - for every datum `D'` with `range D'.p < range D.p`, the Jacquet module of `π` at
    `D'` is a subsingleton.

  This is step 1 of the source proof for actual parabolics.
- `cuspidalEmbedding_of_finite_supercuspidal`: steps 3 and 4. The hypotheses on `k`, `G`
  and `G(k)` are those of the target statement. Let `π : SmoothRep.{0, u, v} ℂ G(k)` be
  irreducible, and fix one actual datum `P, M, U, p, l, r, hp, hl, hr, hmul`. The Levi
  points `M(k)` carry the original Levi point topology `leviPointTopology l hl` and the
  instances `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`.
  Write `J` for `(leviJacquetFunctor p l r hp hr hl hmul).obj π`. Assume three things
  about `J`:
  - `J` is nontrivial;
  - `J` is finitely generated as a module over `MonoidAlgebra ℂ M(k)`;
  - `J` is supercuspidal in the written-out sense of the target. For every actual
    parabolic `p' : P' ⟶ M` with rational Levi `l'`, geometric radical `r'` and
    multiplication isomorphism such that `¬ IsIso p'`, the module
    `(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj J` is a subsingleton.

  Then there is `ρ : SmoothRep.{0, u, v} ℂ M(k)` with carrier in `Type v` such that:
  - `ρ` is irreducible;
  - `ρ` is supercuspidal in the same written-out sense;
  - there is a surjective `J.representation.IntertwiningMap ρ.representation`;
  - there is an injective
    `π.representation.IntertwiningMap ((leviInductionFunctor p l r hp hr hl hmul).obj ρ).representation`.

  The conclusion is the tail of the target's conclusion at the same datum, with the
  same quantifiers and instances.

The two representation-theoretic theorems state their hypotheses in the same
universally quantified form, with `haveI`/`letI`, as `LeviCuspidalEmbeddingStatement`.
That way an assembly can apply them under the target's binders.

## Proofs

**`isIso_of_range_le_range_comp`.** Closed immersions are monomorphisms, so the
hypothesis yields a factorization `f : M ⟶ Q` with `f ≫ q ≫ j = j`
(`SubgroupFunctor.factorOfRangeLE`). Cancelling the monomorphism `j` gives
`f ≫ q = 𝟙 M`. Then `q ≫ f ≫ q = q`, and cancelling the monomorphism `q` gives
`q ≫ f = 𝟙 Q`.

**`ker_ideal_lt_of_range_lt`.** The non-strict inclusion gives a factorization
`f ≫ i' = i`, so `ker i' ≤ ker i` (`Scheme.Hom.le_ker_comp`). Suppose the kernel ideals
on the top affine open were equal. Then the ideal sheaves agree
(`IdealSheafData.ext_of_isAffine`), and `f` is an isomorphism of schemes
(`IsClosedImmersion.isIso_of_ker_eq`). It is then an isomorphism of group schemes,
because the forgetful functors `Grp → Mon → Over → Scheme` reflect isomorphisms. So
`i' = inv f ≫ i`, which gives `range i' ≤ range i` and contradicts strictness.

**`ParabolicDatum.exists_minimal`.** `G.X.left` is affine and locally Noetherian, so
`Γ(G.X.left, ⊤)` is a Noetherian ring. The set of kernel ideals of the inclusions `D.p`,
over the data `D` satisfying `S`, is nonempty and has a maximal element
(`set_has_maximal_iff_noetherian`). Take the corresponding datum `D`. A datum `D'`
satisfying `S` with `range D'.p < range D.p` would have a strictly larger kernel ideal by
`ker_ideal_lt_of_range_lt`, because parabolics are closed subgroups. That contradicts
maximality.

**`normalizedJacquetFunctor_map_surjective`.** Every element of a Jacquet module is a
class `mk 1 b` (`Jacquet.Localization.mk_surjective`). Lift `b` along the surjection to
some `a`. Then `normalizedJacquetFunctor_map_mk` maps `mk 1 a` to `mk 1 b`.

**`exists_minimal_nontrivial_leviJacquet`.** The identity datum has a nontrivial Jacquet
module: its parabolic inclusion `𝟙 G` is an isomorphism, so `fullParabolicLeviJacquetEquiv`
gives a linear equivalence between it and `π`. Smoothness of `G` gives local
finite type. Apply `exists_minimal` to the predicate "the Jacquet module of `π` is
nontrivial". For a strictly smaller `D'`, the module is not nontrivial, so it is a
subsingleton.

**`cuspidalEmbedding_of_finite_supercuspidal`.**

1. The lattice of subrepresentations of `J` is order-isomorphic to its lattice of
   `MonoidAlgebra ℂ M(k)`-submodules (`subrepresentationSubmoduleOrderIso`). That lattice
   is coatomic because `J` is finitely generated. Since `J` is nontrivial, `⊥ ≠ ⊤`, so
   there is a coatom `T₀`.
2. The quotient `ρ = SmoothRep.quotient J T₀` has carrier in `Type v`. It is irreducible
   by `RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom`, and the quotient
   map `SmoothRep.mkQ J T₀` is surjective.
3. For each proper actual parabolic of `M`, the Jacquet functor maps the surjection
   `J → ρ` to a surjection (`normalizedJacquetFunctor_map_surjective`; `jacquetFunctor`
   is a normalized Jacquet functor). Its source is a subsingleton by hypothesis, so its
   target is a subsingleton too. Hence `ρ` is supercuspidal.
4. The published `leviFrobeniusReciprocity.{u, v, v}` at the same datum gives a linear
   equivalence between the intertwiners `π → i_P ρ` and `J → ρ`. The preimage `F` of the
   quotient map is nonzero, since `ρ` is simple and therefore nontrivial, and the
   quotient map is surjective. `π` is irreducible, so the nonzero intertwiner `F` is
   injective (`Representation.IsIrreducible.injective_or_eq_zero`).

## Provenance

The four steps follow the proof of the Corollary in Renard VI.2.1 (printed p. 139 / PDF
p. 145). The Lean route differs from the source in two places, and both are internal
derivations:

- **Minimality.** The source takes a standard parabolic that is minimal for inclusion,
  among the finitely many standard ones. Here every actual parabolic datum is allowed,
  and minimality is taken for the all-test range. A minimal datum exists because kernel
  ideals satisfy the ascending chain condition in the Noetherian coordinate ring of `G`. The same chain
  argument appears in `IsClosedSubgroup.range_comp_iso_eq_of_le`
  (`Rational/PseudoParabolicMinimalityCriterionReduction`).
- **Irreducible quotient.** The source cites VI.1.3 for finite type. Here finite
  generation is a hypothesis, and the quotient is constructed explicitly as a coatom
  quotient, as in `RationalCuspidalEmbeddingProof`.

`ParabolicDatum` and the closed-subgroup lemmas are internal infrastructure.
