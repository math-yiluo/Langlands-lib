# Borel subgroups through a split maximal torus: descent from `k̄`-points

Module `Langlands.GroupScheme.Absolute.RegularCocharacterDescent`. It is derived infrastructure
for clause 3 of `Langlands.GroupScheme.RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`): every Borel subgroup through a split maximal torus
`j : T ⟶ G` represents `P(ν ≫ j)` for some regular cocharacter `ν`. The module reduces this to
two facts about `k̄`-points. The main theorem is conditional on published structure
statements, which it takes as hypotheses and does not prove.

Throughout, `k̄ = AlgebraicClosure k` and `pt[k]` is the test scheme `Spec k̄ ⟶ Spec k` over
`Spec k` (a local notation). A `k̄`-point of `B` is a morphism `pt[k] ⟶ B.X` over `Spec k`.

## Containment of subgroups from `k̄`-points

Let `G` be a group scheme over a field `k`, `i : B ⟶ G` a homomorphism with `B` smooth, and
`iP : P ⟶ G` any homomorphism.

- `coordinateKernel_le_of_algebraicClosurePoints`: if every `k̄`-point of `B` maps under `i`
  into the points of `iP`, then every global function on `G` that vanishes on `P` vanishes on
  `B`, i.e. `coordinateKernel iP ≤ coordinateKernel i`. Proof: for such a function `a`, view
  `s = i^* a` as a morphism `B ⟶ 𝔸¹`. For each `k̄`-point `x` of `B`, write `x ≫ i = y ≫ iP`;
  then `x^* s = y^*(iP^* a) = 0`. Now apply
  `SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat` (ported from the
  Anthropic FLT formalization). It says that two morphisms over `k` from a reduced source,
  whose structure morphism is flat and locally of finite type, to a separated target agree as
  soon as they agree on all `k̄`-points. Its hypotheses hold here. The structure morphism of
  `B` is smooth, hence flat and locally of finite type. `B` is reduced because it is smooth over
  a field (`isReduced_of_smooth_over_field`). `𝔸¹` is separated over `k`. No finite-type
  hypothesis is needed. `B` need not be quasi-compact; for example, the constant group `ℤ` over
  `k` is smooth but not of finite type. So `s = 0`.
- `range_le_of_algebraicClosurePoints`: if moreover `G` is affine and `iP` is a closed
  subgroup, then the points of `B` lie in those of `P` on every test scheme. Proof: on the
  affine `G`, ideal sheaves are determined by global ideals (`Scheme.ker_of_isAffine`), so the
  previous lemma gives `ker iP ≤ ker i`. Mathlib's `IsClosedImmersion.lift` factors the
  underlying morphism of `i` through `iP`. This factorization is over `Spec k`, so each point
  `t` of `B` gives the point `t ≫ lift` of `P` with the same image in `G`.
- `isSolvableGroupScheme_of_isRepresentedBy`: if `iP` represents a subgroup functor `F` and the
  group `F(pt[k])` of `k̄`-points of `F` is solvable, then `P` is solvable
  (`IsSolvableGroupScheme P`). `P(k̄)` embeds into `F(pt[k])` by `iP`, and the points of the
  base change `P_{k̄}` over `Spec k̄` correspond to `P(k̄)` by `baseChangePointsEquiv`.

## The assembly

`isRegular_isRepresentedBy_of_algebraicClosurePoints`. Hypotheses:

- `hLie : DynamicLieStatement` (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.
  (2015), Proposition 2.1.8(1), printed p.53);
- `hSm : DynamicSmoothStatement` and `hCo : DynamicConnectedStatement` (CGP 2.1.8(3),(4));
- `hNeg : RelativeRootNegationStatement`;
- `hobs : RankOneSolvableObstructionStatement`;
- `G` connected reductive over `k`, `j : T ⟶ G` a maximal torus with `T` split, `i : B ⟶ G` a
  Borel subgroup and `f : T ⟶ B` with `f ≫ i = j`, and a cocharacter `ν` of `T`;
- `hpt`: every `k̄`-point of `B` maps under `i` into `P(ν ≫ j)(pt[k])`;
- `hsol`: the group `P(ν ≫ j)(pt[k])` is solvable.

Conclusion: `ν` is regular for `j` (`IsRegularCocharacter j ν`), and `i` represents
`Dynamic.parabolic (groupHom ν ≫ j)`.

Proof:

1. Let `iP : P ⟶ G` be the closed subgroup `Dynamic.Affine.parabolicHom` representing
   `P(ν ≫ j)`. By `hSm` and `hCo` the group `P` is smooth and connected, because `G` is smooth,
   affine and connected. By `hsol` and the previous lemma it is solvable.
2. By `hpt` and `range_le_of_algebraicClosurePoints`, the points of `B` lie in `P(ν ≫ j)` on
   every test scheme, so `i = g ≫ iP` for some `g : B ⟶ P`
   (`SubgroupFunctor.IsRepresentedBy.liftOfLE`).
3. `B` is maximal among smooth connected solvable closed subgroups, so `g` is an isomorphism.
   Hence the points of `i` are exactly `P(ν ≫ j)`, and `i` represents it.
4. Regularity. Suppose `⟨α, ν⟩ = 0` for a root `α`. By `hNeg`, `-α` is also a root
   (`neg_mem_roots_of_relativeRootNegation`), and `⟨-α, ν⟩ = 0`. Choose nonzero vectors in
   `weightSpace j α` and `weightSpace j (-α)`. Both lie in `nonnegativeWeightSpan j ν`, so by
   `hLie` both lie in the image of `Lie(B)`
   (`exists_lieKernel_of_mem_nonnegativeWeightSpan`). This contradicts `hobs` applied to the
   smooth connected solvable closed subgroup `B` through `j`.

## Provenance

Milne, *Algebraic Groups* (2017), proves the corresponding claim (every Borel subgroup
containing `T` is `P(λ)` for a regular `λ`) in Theorem 21.32 (statement printed p.434, PDF
p.450; proof printed pp.434–435, PDF pp.450–451). For a general field he composes injective
maps from Weyl chambers to Borel subgroups of `G` containing `T`, then to those of `G_{k̄}`
containing `T_{k̄}`, then back to Weyl chambers. Milne's Borel subgroups over `k` are those
that become Borel subgroups over `k̄`. The published `IsBorelSubgroup` is instead maximality
among subgroups defined over `k`, so this module replaces that step:

- the conjugacy argument over `k̄` (module `BorelDynamicConjugacy`) is to supply `hpt` and
  `hsol`;
- containment is descended to `k` through `k̄`-points, because `B` is reduced;
- the published maximality of `B` over `k` then identifies `B` with `P(ν ≫ j)`;
- regularity comes from the rank-one obstruction (Milne, Lemma 21.28, printed p.433) with
  `hLie` and root symmetry, instead of from Weyl chambers.

The containment lemmas are internal. The Library module `RationalSubgroupContainment`
(`SubgroupFunctor.range_le_of_algClosed_points`) proves the analogous containment over an
algebraically closed field from rational points, via Jacobson schemes. The present lemmas work
over an arbitrary field from `k̄`-points.
