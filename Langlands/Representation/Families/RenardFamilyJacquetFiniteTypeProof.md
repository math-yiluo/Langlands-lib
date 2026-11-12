# Renard VI.8.3: Jacquet modules of families preserve finite generation

Author: Worker 5188. Module
`Langlands.Representation.Families.RenardFamilyJacquetFiniteTypeProof`,
namespace `Langlands.Renard.AlgebraicFamily`.

The module proves the unchanged VI.8.3 Proposition
`JacquetFiniteTypeStatement.{u, uB, uV}` of
[RenardFamilyParabolicStatements](RenardFamilyParabolicStatements.md), at its
own independent universe parameters:

```lean
theorem jacquetFiniteType : JacquetFiniteTypeStatement.{u, uB, uV}
```

No hypothesis is added. The compactness of `P(F)\G(F)` that the argument needs
is not assumed: it is obtained inside the proof from three published Library
theorems (see "Statement" below).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.8.3 Proposition and the remark after it, printed p. 191 /
PDF p. 197. Literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard
gives no separate proof: the Proposition generalizes VI.1.3 to `(G, B)`-modules,
and "le point crucial est la compacité de `P\G`, et donc la finitude de
`P\G/K`". The implemented argument is the one of the published `B = ℂ` proof
`Langlands.Aubert.General.JacquetFiniteGeneration.finite_of_compactQuotient`,
rewritten here for an arbitrary commutative `ℂ`-algebra `B` and the family
Jacquet functor `jacquetRepresentation` of
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md). The reading of
"de type fini" as finite generation over the group algebra is the statement's
(its correspondence note 5).

## Proof

### `Generation`

`finite_asModule_of_translateCover` is an abstract finite-generation criterion.
Let `ρ : Representation B H V` with `ρ.asModule` finite over `B[H]`, let
`J : Representation B M W`, and let `q : V →ₗ[B] W` be surjective. Suppose that
for each `v ∈ V` there is a finite set `t ⊆ H` such that every
subrepresentation `S` of `J` containing all `q (ρ i v)`, `i ∈ t`, contains all
`q (ρ g v)`, `g ∈ H`. Then `J.asModule` is finite over `B[M]`.

Proof: take finitely many generators `s` of `ρ.asModule` and let `N` be the
`B[M]`-span of the finite set `{q (ρ i v) : v ∈ s, i ∈ t v}`, seen as a
subrepresentation `S` of `J` (`Subrepresentation.ofSubmodule'`). By hypothesis
`q (ρ g v) ∈ S` for all `v ∈ s` and `g`. The vectors `w` with `q (ρ g w) ∈ S` for
all `g` form a subrepresentation `C` of `ρ` (an intersection of preimages,
stable because `ρ (a) ρ (g) = ρ (a g)`), which contains `s` and hence its
`B[H]`-span, which is everything. Taking `g = 1` and using surjectivity of `q`
gives `N = ⊤`.

### `Parabolic`

Let `G` be a locally compact nonarchimedean group with
`h : IsSemidirectDecomposition P M U` and `U` closed, and let `B` be a
commutative `ℂ`-algebra.

- `mk_parabolic_mem`: if a subrepresentation `S` of the normalized Jacquet
  module `jacquetRepresentation ρ U M hU _` contains the class `[v]`, it contains
  `[ρ(p) v]` for every `p ∈ P`. Write `p = m n` with `m = h.projection p ∈ M`
  and `n = m⁻¹ p ∈ U`. Then `[ρ(n) v] = [v]` in the `U`-coinvariants
  (`Jacquet.Localization.mk_apply_subgroup` with the trivial character), and by
  `jacquet_action_mk` the normalized action gives
  `J(m) [v] = χ(m) • [ρ(m) ρ(n) v] = χ(m) • [ρ(p) v]`, where
  `χ(m) = jacquetCharacter … m` is a unit of `B`. Since `J(m)[v] ∈ S` and `S` is
  a `B`-submodule, `[ρ(p) v] ∈ S` (`Submodule.smul_mem_iff'` for the unit).
  So the normalizing character does not affect generation.
- `finite_jacquet_comp_of_compactQuotient`: assume moreover
  `CompactSpace (Induction.LeftQuotient P)`, `ρ` smooth and `ρ.asModule` finite
  over `B[G]`. For every surjective group homomorphism `φ : M' →* M`, the pulled
  back representation `(jacquetRepresentation ρ U M hU _).comp φ` is finite over
  `B[M']`. Apply `finite_asModule_of_translateCover` with
  `q = Jacquet.Localization.mk ρ U 1` (surjective by `mk_surjective`). For `v`,
  smoothness gives an open subgroup `K` fixing `v`, and compactness of `P\G`
  gives a finite `t` with `G = ⋃_{i ∈ t} P i K`
  (`Induction.exists_finset_doubleCoset_cover`). For `g = p i k`,
  `ρ(g) v = ρ(p) ρ(i) v`. A subrepresentation `S` of the pulled back action is a
  subrepresentation of `jacquetRepresentation` itself, because `φ` is
  surjective. So if `[ρ(i) v] ∈ S` for all `i ∈ t`, then `mk_parabolic_mem`
  gives `[ρ(g) v] ∈ S`.

### `Statement`

`jacquetFiniteType` introduces the binders of `JacquetFiniteTypeStatement`,
installs `hG.isAffineHom` and the canonical point topology exactly as the
statement does, and obtains the compactness instance
`CompactSpace (Induction.LeftQuotient (pointImage p))` from three published
theorems:

- `Langlands.Aubert.General.RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic`
  (module `ArbitraryParabolicFiniteSupportReduction`), which derives this exact
  compactness from `GroupScheme.ParabolicDynamicStatement` and
  `BruhatTits.DynamicParabolicQuotientCompactStatement`;
- `Langlands.GroupScheme.parabolicDynamic`, the published proof of
  `ParabolicDynamicStatement` (every parabolic is `P(λ)` for a rational
  cocharacter `λ`);
- `Langlands.BruhatTits.dynamicParabolicQuotientCompact`, the published proof of
  `DynamicParabolicQuotientCompactStatement` (compactness of the quotients of
  the rational points by a dynamic parabolic).

In the source this compactness is Renard's V.5.1 Corollary (printed p. 123 /
PDF p. 129). With the topology `leviPointTopology l hl` on `rationalPoints M`
(used only to form `leviPointsEquiv`), `leviJacquetRepresentation … ρ` is by
definition `(jacquetRepresentation ρ (pointImage (r ≫ p)) (pointImage (l ≫ p)) …).comp`
of the group isomorphism `leviPointsEquiv p l hp hl` from `M(F)` onto the Levi
image. The theorem applies `finite_jacquet_comp_of_compactQuotient` to the
published semidirect decomposition `isSemidirectDecomposition_pointImage`, the
closed radical image `isClosed_pointImage_comp`, and `φ` this isomorphism, which
is surjective.

## Hypotheses not used

The proof does not use flatness of `V`, the Noetherian, finite-type and reduced
hypotheses on `B`, or that `B` is a `ℂ`-algebra beyond the definitions of the
normalizing characters: the criterion holds for any commutative coefficient
ring, and the normalizing character only contributes units of `B`. Compactness
of `P(F)\G(F)` is essential: it makes `P\G/K` finite, so finitely many
translates suffice for each generator.
