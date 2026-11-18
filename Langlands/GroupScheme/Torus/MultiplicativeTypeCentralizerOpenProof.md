# Proof: the centralizer of a subgroup of multiplicative type is open in its normalizer

Worker 1324, with Worker 234 (reduction to the split case).

Module: `Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerOpenProof`.

`Langlands.GroupScheme.multiplicativeTypeCentralizerOpen` proves
[`MultiplicativeTypeCentralizerOpenStatement.{u}`](MultiplicativeTypeCentralizerOpenStatement.md)
for every universe `u`. This is Milne, *Algebraic Groups* (2017), Corollary 12.40, in the
form "`C_G(H)` is an open subgroup of `N_G(H)`". The data are a field `k`, a group scheme
`G` over `Spec k`, a closed subgroup `i : H ⟶ G` of multiplicative type, representatives
`n : N ⟶ G` of the all-test normalizer and `c : C ⟶ G` of the all-test centralizer of
`range i`, and `f : C ⟶ N` with `f ≫ n = c`. The goal is that `f.hom.hom.left` is an open
immersion.

## Proof

The Lean proof is a single application that combines two published results.

1. **Reduction to the split case.**
   `multiplicativeTypeCentralizerOpen_of_diagonalizable`
   ([`MultiplicativeTypeCentralizerOpenReduction`](MultiplicativeTypeCentralizerOpenReduction.md))
   proves that `DiagonalizableCentralizerOpenProperty.{u}` implies the target statement.
   The property is stated over every field `k` and every finitely generated abelian
   group `M`, torsion allowed. It asks that for an arbitrary group scheme `G` over `Spec k`
   and a homomorphism `i : D(M) ⟶ G` that is a monomorphism of schemes, if
   `n : N ⟶ G` represents `torusNormalizer i` and `c : C ⟶ N` represents the preimage
   `(torusCentralizer i).comap n`, then `c` is an open immersion.
   The reduction proceeds as follows. It takes the splitting field `K` and the
   character group `M` from `IsMultiplicativeType H`, then base-changes `G`, `i`, the
   representatives and the subgroup functors to `K`, using the commutation of normalizers
   and centralizers with base change. It identifies `f` as a representative of the preimage
   centralizer, applies the split property over `K`, and descends openness of `f` along
   the fpqc morphism `Spec K ⟶ Spec k`.

2. **The split case.**
   `diagonalizableCentralizer_isOpenImmersion_field`
   ([`DiagonalizableCentralizerOpen`](DiagonalizableCentralizerOpen.md)) proves exactly
   the body of `DiagonalizableCentralizerOpenProperty`, with binders in the same order
   `k, M, G, N, C, i, hi, n, c, hn, hc`. So the property is the lambda term
   `fun k _ M _ _ G N C i hi n c hn hc =>
   diagonalizableCentralizer_isOpenImmersion_field k M G N C i hi n c hn hc`.
   It is the field case of a result over any affine base `Spec R`. A point of the
   normalizer acts on the characters of `D(M)` by conjugation. On affine charts the action
   on each element of a finite generating set of `M` is a grouplike element of the
   coordinate group algebra. The action is trivial exactly where the idempotent
   coefficients of these elements equal `1`. This gives an open centralizer locus
   `DiagonalizableConjugation.centralizerLocus` in `N`, taking `g = n` as the universal
   normalizer point. Both `c` and the inclusion of this open subscheme into `N` factor
   through each other, so `C` is isomorphic to the open subscheme and `c` is an open
   immersion.

The route differs from Milne's proof, which applies the rigidity theorem 12.36 to the
conjugation family `N_G(H)° × H → H`. Here openness comes from the explicit idempotent
locus in the split case, followed by fpqc descent.

The target's finite-type hypotheses on `G` (`LocallyOfFiniteType`, `QuasiCompact`) are
not used: the reduction carries them but does not need them. Closedness of `i` is used
only to obtain the monomorphism that the split case requires.

## Dependencies

The module imports
[`Torus.MultiplicativeTypeCentralizerOpenReduction`](MultiplicativeTypeCentralizerOpenReduction.md)
(which imports the statement) and
[`Torus.DiagonalizableCentralizerOpen`](DiagonalizableCentralizerOpen.md). It adds no
definitions and no axioms; the theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`.
