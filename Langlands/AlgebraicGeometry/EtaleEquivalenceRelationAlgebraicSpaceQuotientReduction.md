# Reduction of the étale quotient theorem to fppf descent

Authors: Worker 1001.

This module proves the algebraic-space quotient theorem for étale equivalence relations
(Stacks Project Theorem 65.10.5, Tag [02WW](https://stacks.math.columbia.edu/tag/02WW),
retained as `stacks-etale-equivalence-relations-2026-11-01`) from one hypothesis: the sheaf
form of effective fppf descent for separated, locally quasi-finite morphisms locally of
finite type (Tag [02W8](https://stacks.math.columbia.edu/tag/02W8)). The route differs from
the source, as explained below.

## Results

- `EtaleEquivalenceRelation.isOverEquivRel E b hb`: for an étale equivalence relation
  `E : EtaleEquivalenceRelation.{u}` and `b : E.U ⟶ S` with `E.t ≫ b = E.s ≫ b`, the slice
  maps `Over.homMk E.t, Over.homMk E.s hb.symm : Over.mk (E.t ≫ b) ⟶ Over.mk b` satisfy
  `RelationQuotient.IsOverEquivRel`. The four conditions are the fields `mono_lift`,
  `refl`, `symm` and `trans` of `E`, applied to the underlying schemes of the test
  objects. The witnesses lie over `S` because composing with `E.t ≫ b` recovers the
  structure morphism.
- `etaleEquivalenceRelationAlgebraicSpaceQuotient_of (hD)`: from
  `hD : FppfSeparatedLocallyQuasiFiniteDescentStatement.{u}` it proves
  `EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}`.

## Proof of the reduction

Let `U`, `R`, `t`, `s` be the slice data of the statement. Take
`Q = RelationQuotient.quotientSheaf t s`, the fppf sheafification of the presheaf quotient of
the points of `U` by the relation, and `a = RelationQuotient.quotientMap t s`.

1. The kernel pair of `a` is `(t, s)` (`RelationQuotient.isPullback_quotientMap`), and `a`
   is fppf locally surjective (`RelationQuotient.isLocallySurjective_quotientMap`).
2. `t.left = E.t` is étale, hence locally of finite type. So `Q` has representable diagonal
   by `KernelPair.hasRepresentableDiagonal_of_isPullback hD`.
3. `s.left = E.s` is étale, so `a` is étale (`KernelPair.isEtale_of_isPullback`).
4. A locally surjective étale map is surjective
   (`OpenSubfunctorImages.isSurjective_of_isEtale_isLocallySurjective`).

Therefore `Q` with the atlas `a` is an algebraic space in the sense of
`AlgebraicSpace.Basic`, and `a` witnesses the conclusion: it is étale and surjective, and the
kernel pair square is the pullback from step 1.

## Comparison with the source

The source reduces to a disjoint union of affine opens of `U`, proves the affine case with
Lemma 65.10.4 (Tag [0265](https://stacks.math.columbia.edu/tag/0265)), and glues with
Lemmas 65.8.4 and 65.8.5. In the affine case affineness is used to make `R`, and hence `t`,
separated. The first step of that proof needs this: it shows that the quotient map is
representable by descending `T ×_{U/R} U`, which is locally a base change of `t`. The third
step proves that the diagonal is representable. It uses only that `(t, s) : R ⟶ U ×_S U` is a
monomorphism, so it works for any `U`.

The proof here performs the diagonal step first (`KernelPairDiagonal`, on equalizer loci of
sections) and obtains representability of `a` from the representable diagonal
(`Functor.relativelyRepresentable.of_diag`). Étaleness then follows by fppf locality, as in
Lemma 65.10.3 (Tag [02WV](https://stacks.math.columbia.edu/tag/02WV)) (`KernelPairEtale`).
Hence neither the reduction to affine pieces nor the gluing is needed.
