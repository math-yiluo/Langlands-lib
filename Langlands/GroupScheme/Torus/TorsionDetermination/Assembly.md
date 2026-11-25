# Corollaries 4.8 and 4.9 of SGA 3 IX from the torsion-closed immersion lemma

This module is an internal step of the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement`. It derives the
three parts of that statement from one hypothesis, the *torsion-closed immersion lemma*
`TorsionClosedImmersionIsIso`, which is proved in [`Reduction`](Reduction.md) from the core
case for the group-algebra models `Spec R[Λ]`. All declarations are in the namespace
`Langlands.GroupScheme.TorsionDetermination`; `PointLifts` and `IsTorsionClosed` are defined in
[`Descent`](Descent.md).

## The hypothesis

`TorsionClosedImmersionIsIso.{u} : Prop` says: for every scheme `S : Scheme.{u}`, every
`G : GroupScheme S` with `RelativeMultiplicativeType.IsMultiplicativeType G`, every scheme
`Z` and every immersion of schemes `j : Z ⟶ G.X.left` with `IsTorsionClosed G j`, the
morphism `j` is an isomorphism. In words: an immersion into a group of multiplicative type
through which all torsion points lift, and whose lifting points are closed under
multiplication, is an isomorphism. Unlike SGA 3, the subgroup is not required to be a
group scheme; this lets parts 4.8 a) and b) apply the lemma to equalizers and
intersections directly.

## Auxiliary results

- `lifts_iff_mem_range`: for a homomorphism `h : H ⟶ G`, a point `x : T ⟶ G.X` lifts
  through the underlying morphism of schemes `h.hom.hom.left` exactly when
  `x ∈ (SubgroupFunctor.range h).carrier T`. A lift `a : T.left ⟶ H.X.left` is
  automatically a morphism over `S`, because `h.hom.hom` is.
- `isTorsionClosed_of_range`: if `SubgroupFunctor.range h` contains every torsion point,
  then `h.hom.hom.left` is torsion-closed (the range is a subgroup, hence closed under
  multiplication).
- `isIso_of_isIso_left`: a homomorphism of group schemes whose underlying morphism of
  schemes is an isomorphism is an isomorphism; the forgetful functors
  `Grp (Over S) ⥤ Mon (Over S) ⥤ Over S ⥤ Scheme` reflect isomorphisms.

## The three parts

Each part assumes `hM : TorsionClosedImmersionIsIso.{u}`.

- `part_c` (**SGA 3 IX 4.9**): for `G` of multiplicative type and a homomorphism
  `h : H ⟶ G` whose underlying morphism is an immersion and whose range contains every
  point `x` with `x ^ n = 1`, `n > 0`: `h.hom.hom.left` is torsion-closed, so by `hM` it is
  an isomorphism of schemes, and `h` is an isomorphism by `isIso_of_isIso_left`.
- `part_b_le` and `part_b` (**SGA 3 IX 4.8 b)**): for subgroups `h₁ : H₁ ⟶ G` and
  `h₂ : H₂ ⟶ G` with `H₁` of multiplicative type and `h₂` an immersion, if every torsion
  point of `G` in the range of `h₁` is in the range of `h₂`, then the pullback
  `pullback.snd h₂.hom.hom.left h₁.hom.hom.left` (the intersection `H₁ ∩ H₂` as a
  subscheme of `H₁`) is an immersion into `H₁`. A point `y` of `H₁` lifts through it exactly
  when `y ≫ h₁.hom.hom` lies in the range of `h₂` (`lifts_pullback_iff`,
  `lifts_iff_mem_range`); these points are closed under multiplication since `h₁` is a
  homomorphism and the range of `h₂` is a subgroup, and they contain every torsion point of
  `H₁` by hypothesis. By `hM` the pullback morphism is an isomorphism, so the range of `h₁`
  is contained in the range of `h₂` (`SubgroupFunctor.le_def`). `part_b` combines the two
  inclusions. This is SGA's argument: `H₁ ∩ H₂` is a subgroup of each `Hᵢ` majorizing the
  `ₙHᵢ`, so 4.9 applies.
- `part_a` (**SGA 3 IX 4.8 a)**): for `H` of multiplicative type and homomorphisms
  `u v : H ⟶ G` agreeing on all torsion points of `H`, the equalizer
  `equalizer.ι u.hom.hom.left v.hom.hom.left` is an immersion (Mathlib). A point `x` of `H`
  lifts through it exactly when `x ≫ u.hom.hom = x ≫ v.hom.hom`, and these points are
  closed under multiplication (`MonObj.mul_comp`) and contain all torsion points by
  hypothesis. By `hM` the equalizer inclusion is an isomorphism, so the identity point of
  `H` lifts, giving `u.hom.hom = v.hom.hom` and `u = v` (`Grp.hom_ext`). SGA instead applies
  4.8 b) to the graphs of `u` and `v` in `H × G`; the equalizer is the intersection of
  these graphs, and using it directly avoids forming products.
- `statement_of_torsionClosedImmersionIsIso`: the statement
  `MultiplicativeTypeTorsionDeterminationStatement.{u}` follows from `hM`, by `part_a`,
  `part_b` and `part_c`.

## Source

SGA 3, Exposé IX (Gille–Polo recomposed edition, registered as
`sga3-expose-ix-gille-polo-2009`), Corollaires 4.8 and 4.9 and their proofs, p.47–48
(margin 57–58). SGA deduces 4.9 from the density theorem 4.7; here 4.9 and both parts of
4.8 are deduced from `TorsionClosedImmersionIsIso` instead, whose proof is in
[`Reduction`](Reduction.md).
