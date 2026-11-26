# Points of a torus centralizer lie in Borel subgroups containing the torus

`Langlands.GroupScheme.torusCentralizerBorelCover` proves
`Langlands.GroupScheme.TorusCentralizerBorelCoverStatement.{u}` for every
universe `u`. For a closed torus `s : S.toGrp ⟶ G` in a smooth connected affine
group over an algebraically closed field `k`, it lifts each rational point
of `torusCentralizer s` to a Borel subgroup of `G` containing `S`.
[Target statement](TorusCentralizerBorelCoverStatement.md)

## Lean proof

1. Finite Galois splitting makes `S` split over `k` by
   `IsTorus.isSplitTorus_of_finiteGaloisSplitting` and `torusFiniteGaloisSplitting`.
   Then `torusCentralizer_hasSmoothClosedRepresentative` gives a smooth closed
   subgroup `c : C ⟶ G` representing `torusCentralizer s` on all test schemes.
   Its structure morphism is affine by `IsClosedSubgroup.isAffineHom`, and
   `IsTorus.connectedSpace_centralizer` gives connectedness.
2. The representation identifies centralizer membership with membership in
   `SubgroupFunctor.range c`. Applying `SubgroupFunctor.mem_range` yields a
   rational point `x` of `C` mapping to `g`. Applying `borelPointContainment` to
   `x` yields a Borel subgroup `d : D ⟶ C` and a rational point `y` of `D`
   mapping to `x`. [Borel point containment](BorelPointContainmentProof.md)
3. The converse in `torusCentralizerBorel` gives a Borel subgroup `i : B ⟶ G`
   containing `S` with `range (d ≫ c) = range c ⊓ range i`. The point `y`
   witnesses that `g` lies in `range (d ≫ c)`. The intersection equality
   gives membership in `range i`, and `SubgroupFunctor.mem_range` gives the
   required lift `b` of `g`. [Borels of a torus centralizer](TorusCentralizerBorelProof.md)

## Source

The target is Lemma 17.37, printed p. 363, of James S. Milne, *Algebraic Groups*
(2022 corrected reprint, `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`).
Milne applies the Borel fixed-point theorem to the closed locus in `G/B` fixed
by `g`. The Lean proof combines Borel point containment (Corollary 17.34),
connectedness of torus centralizers (Theorem 17.38), and the Borel intersection
theorem (Theorem 17.46), using their Library proofs.
