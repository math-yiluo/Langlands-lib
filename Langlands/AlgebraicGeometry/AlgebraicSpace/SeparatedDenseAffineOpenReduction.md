# Dense affine open subspaces, assuming 03BM and 03JE

This module defines the internal proposition `SeparatedDenseAffineOpenLFTProp`: the
published `SeparatedDenseAffineOpenStatement` with the additional conclusion
`LocallyOfFiniteType V.hom` for the affine open `V`. It is a derived strengthening, not a
statement from the literature. Like the published statement, it concerns a separated algebraic
space `X` over a field `k` with an etale surjective atlas `a : U ⟶ X` from an affine scheme `U`
locally of finite type over `k`. The affine atlas is essential, since step 4 below uses that
`U` is Noetherian. The group-space proof applies it only to such spaces, namely the images
of finite coproducts of affine charts in `GroupLocalCharts`. `separatedDenseAffineOpenLFT_of h03BM h03JE hfl` proves it. The affine `V`
is a finite flat quotient of an open of the atlas, so `FiniteFlatSourceDescent` applies.
`separatedDenseAffineOpen_of h03BM h03JE hfl` proves `SeparatedDenseAffineOpenStatement.{u}`.
Both theorems take as hypotheses the statements of Stacks 03BM and finite-set 03JE and the
proposition `FiniteLocusInvariantProp` (invariance of the finite locus). The last is proved as
`FiniteLocus.finiteLocus_invariant`, and the group-space proof supplies all three.

The helper `noetherianSpace_of_isAffine_of_locallyOfFiniteType` says that an affine scheme
locally of finite type over a field is a Noetherian space (its ring is a finitely generated
algebra over a field).

Proof (derived from the proofs of Stacks 06NH and 06NG, third proof, as documented in the
statement's Markdown):
1. `R = U ×_X U` is represented, by the representable diagonal. Its projections `t, s` are
   etale, and `R` is affine because the diagonal is closed (`AffineIntersections`).
2. `(t, s)` is an equivalence relation (`AtlasRelation`).
3. The finite locus `W` of `s` is invariant and contains every generic point
   (`FiniteLocus`, generic finiteness).
4. `U` is Noetherian, so the set `E` of generic points is finite. It is saturated because
   `s` has discrete fibres and `t` is flat. Prime avoidance gives a basic open `D(f)` with
   `E ⊆ D(f) ⊆ W`.
5. 03JE on the restricted relation over `W` gives an invariant affine open `V'` of `W`
   containing `E`. Its image `V ⊆ U` is affine, invariant and contains `E`.
6. 03BM on the restricted relation over `V` gives an affine `M` and a finite flat finitely
   presented surjection `q : V → M` with `IsPullback t s q q`. `M` lies over `Spec k` by
   `EffectiveEpi.desc`.
7. The sheafified image `Q ⊆ X` of `a|_V` is an open subfunctor. Worker 1150's
   `exists_iso_of_locallySurjective_of_same_kernel` gives `Y(M) ≅ Q`; the kernel condition
   comes from the pullback square of `q` and the kernel pair.
8. The square with `Y(q)`, `V ↪ U`, `Y(M) ↪ X` and `a` is a pullback. A test point of `U`
   whose image in `X` lies in `Q` factors through `V`: points of the covering sieve lift to
   `R`, and `V` is invariant.
9. The density of `V` follows from `E ⊆ V` and the density of the generic points.
