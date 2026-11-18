# Trivial radical and quotient by the radical over a perfect field: proof

Author: Worker 895.

The theorem `Langlands.GroupScheme.perfectFieldSemisimpleRadical` proves the
unchanged published proposition
`Langlands.GroupScheme.PerfectFieldSemisimpleRadicalStatement.{u}` (module
`Langlands.GroupScheme.Reductive.PerfectFieldSemisimpleRadicalStatement`) at an
arbitrary universe `u`, with no added hypothesis: for every field `k : Type u`
with `[PerfectField k]` and every group scheme `G` over `Spec k` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`,

1. `HasTrivialSolvableRadical G → IsSemisimple G`, and
2. for every `r : R ⟶ G` with `IsSolvableRadical r` and every `q : G ⟶ Q` with
   `IsAffineHom Q.X.hom` and
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q`, `IsSemisimple Q`.

The module also proves four auxiliary theorems in the namespace
`Langlands.GroupScheme.PerfectFieldSemisimpleRadical`. No helper module is
added. The proof uses only published Library results:

- `separableAlgebraicSolvableRadical`
  (`Langlands.GroupScheme.Rational.SeparableSolvableRadicalProof`), the proof of
  `SeparableAlgebraicSolvableRadicalStatement` (Milne, *Algebraic Groups*
  (2017), Proposition 19.1: a solvable radical stays a solvable radical after a
  separable algebraic field extension);
- `IsGeometricSolvableRadical.isSemisimple_quotient`
  (`Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction`):
  over any field, an affine fppf quotient of a smooth connected affine group by
  a geometric solvable radical is semisimple;
- `solvableRadicalExistence`
  (`Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof`): every smooth
  connected affine group over a field has a represented solvable radical;
- `mem_range_kernelι_iff` (`Langlands.GroupScheme.CentralIsogeny.Basic`): a point
  lies in the image of the kernel inclusion of `f` exactly when its composite
  with `f` is `1`;
- Mathlib's instance `Algebra.IsAlgebraic.isSeparable_of_perfectField`: an
  algebraic extension of a perfect field is separable.

The predicate `IsGeometricSolvableRadical r` (from
`Langlands.GroupScheme.Rational.LeviSubgroup`) is by definition the conjunction
of `IsSolvableRadical r` and `IsSolvableRadical` of the base change of `r` along
`toAlgebraicClosure k`.

## Auxiliary theorems

**`range_kernelι_id`.** For a group scheme `G` over any scheme,
`SubgroupFunctor.range (kernelι (𝟙 G)) = ⊥`. Proof as implemented: by
extensionality it suffices to compare the carriers on each test `T`. By
`mem_range_kernelι_iff`, a point `x : T ⟶ G.X` is in the image of the kernel
inclusion exactly when `x ≫ (𝟙 G).hom.hom = 1`, that is, when `x = 1` (`simp`),
which is membership in `⊥` (`SubgroupFunctor.bot_carrier`, `Subgroup.mem_bot`).

**`isFppfQuotient_id`.** `RelativeRoot.IsFppfQuotient ⊥ (𝟙 G)`. The underlying
morphism of schemes of `𝟙 G` is definitionally `𝟙 G.X.left`, which is flat,
surjective and locally of finite presentation by Mathlib's instances for
identities; the kernel condition is `range_kernelι_id`.

**`isGeometricSolvableRadical_of_perfectField`.** Assume
`SeparableAlgebraicSolvableRadicalStatement.{u}`. Let `k : Type u` be a perfect
field, `G` a smooth connected affine group over `k` and `r` with
`IsSolvableRadical r`. Then `IsGeometricSolvableRadical r`. Proof as implemented:
the first component is `r` itself. For the second, `AlgebraicClosure k : Type u`
is algebraic over `k`, hence separable over the perfect field `k` (Mathlib
instance above), so the assumed statement applied to `K = AlgebraicClosure k`
gives `IsSolvableRadical` of the base change of `r` along
`Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`. This
morphism is exactly `toAlgebraicClosure k`, an abbreviation of the same term,
so the result is the second component as stated.

**`perfectFieldSemisimpleRadical_of_separableAlgebraic`.**
`SeparableAlgebraicSolvableRadicalStatement.{u} → PerfectFieldSemisimpleRadicalStatement.{u}`.
Proof as implemented, after introducing `k`, `G` and the three hypotheses on
`G` (also installed as local instances):

- Part 2. Given `r`, `Q` and `q` as in the statement,
  `isGeometricSolvableRadical_of_perfectField` makes `r` a geometric solvable
  radical, and `IsGeometricSolvableRadical.isSemisimple_quotient` applied to `q`
  and the quotient hypothesis gives `IsSemisimple Q`.
- Part 1. Assume `HasTrivialSolvableRadical G`. `solvableRadicalExistence`
  gives `r : R ⟶ G` with `IsSolvableRadical r`. The fields of `r` (closed
  subgroup; `R` smooth, connected and solvable; normal image) are exactly the
  hypotheses of `HasTrivialSolvableRadical G`, so `SubgroupFunctor.range r = ⊥`.
  Rewriting with this equality, `isFppfQuotient_id` shows that the identity
  `𝟙 G : G ⟶ G` is an fppf quotient by `SubgroupFunctor.range r`; the target `G`
  is affine. As in Part 2, `r` is a geometric solvable radical, and
  `IsGeometricSolvableRadical.isSemisimple_quotient` applied to `𝟙 G` gives
  `IsSemisimple G`.

## Main theorem

`perfectFieldSemisimpleRadical` applies
`perfectFieldSemisimpleRadical_of_separableAlgebraic` to the published proof
`separableAlgebraicSolvableRadical`.

## Relation to the source

Milne, *Algebraic Groups* (2017), Proposition 19.2 (printed p. 398), source ID
`milne-2017-algebraic-groups`. Milne proves (a) from Proposition 19.1 applied to
`k^a/k`, and (b) by showing that the inverse image of `R(G/RG)` in `G` is a
smooth connected solvable normal subgroup, hence equal to `RG`, so that
`R(G/RG) = e`, and then applying (a). The implemented proof also rests on
Proposition 19.1 for `k^a/k`, but proceeds differently: it derives (b) directly
from the Library's theorem that a quotient by a geometric solvable radical is
semisimple (whose proof contains the inverse-image argument after base change
to the algebraic closure), and derives (a) from (b) using the identity map as
the quotient of `G` by its trivial radical.
