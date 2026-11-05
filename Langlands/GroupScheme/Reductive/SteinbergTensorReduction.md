# The positive-characteristic conjugation map from Steinberg tensor embeddings

This internal derived reduction proves that
`SteinbergTensorEmbeddingStatement` implies
`SimplyConnectedPositiveCharConjugationMapStatement`, at every universe `u`.
The implication is the proposition
`SimplyConnectedPositiveCharConjugationMapFromSteinbergStatement`, and the
theorem `simplyConnectedPositiveCharConjugationMap_of_steinberg` proves it.
It does not prove either proposition on its own. The deep Steinberg and
exhaustion input stays an explicit assumption.

## Helper

`AffineCoordinates.nontrivial_algebra` shows that the coordinate algebra of an
affine group scheme over a field is nontrivial. The counit of the coordinate
bialgebra is a `k`-algebra map to the field `k`, and the domain of a ring map
to a nontrivial ring is nontrivial.

## Proof

Fix `k`, `p`, a simply connected `G`, an actual finite representation `ρ`, and a
nonzero vector `v` that is fixed on all tests.

1. **Affineness.** Simple connectedness includes semisimplicity, hence connected
   reductivity, so the structure morphism of `G` is affine. Its total space is
   then affine (`isAffine_of_isAffineHom`). This supplies the binder of the
   embedding statement.
2. **Torus-invariant regular target.** The embedding statement gives a
   diagonalizable `j`. The published theorem
   `Chevalley.exists_affine_finite_diagonalizable_regular_map_to_one`
   (`AffineReynoldsRegular`) then gives:
   - a finite subspace `V` of the coordinate algebra with basis `b`;
   - right stability `hV`;
   - an intertwiner `C` from `ρ` to the finite regular representation on `V`;
   - left `j`-invariance of `V` on all tests;
   - the normalization `∑ l, (C v)_l • b_l = 1`.
3. **Tensor embedding.** Applying the embedding statement to this `V` gives
   `m`, `σ`, `π` and an injective intertwiner `E` from the regular
   representation on `V` to `σ.tensor π`, with `σ` rationally irreducible.
4. **Nonvanishing.** `C v ≠ 0`. Otherwise the normalization would give
   `0 = 1` in the coordinate algebra, contradicting the helper. Since `E` is
   injective, `(E * C) v = E (C v) ≠ 0`.
5. **Positive size.** `m > 0`, because a vector indexed by `Fin 0 × Fin 0` is
   zero.
6. **Conjugation map.** By `Intertwines.comp`, `E * C` intertwines `ρ` with
   `σ.tensor π`. The published adapter
   `MatrixRepresentation.ConjugationLinearMap.exists_eval_eq_one_of_tensor`
   (`NondegenerateTensorConjugation`) needs only irreducibility of `σ` and the
   nonzero tensor image of the fixed vector. It gives an actual conjugation map
   `φ : ConjugationLinearMap ρ σ` whose linear matrix at `v` is exactly the
   identity.
7. **Conclusion.** The target follows with scalar `a = 1`.

## Scope

No characteristic or simple-connectedness argument is used beyond affineness.
Positive characteristic and simple connectedness matter only through the
assumed embedding statement. No self-duality, determinant, symmetric-power or
`p`-power dimension statement is used or claimed.

The route is the linear-algebra part of the proof sketch of Theorem A.1.0,
(a) implies (b), in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
third enlarged edition (1994), Appendix to Chapter 1, Section A, printed
p.192 (`mumford-fogarty-kirwan-1994-git-3rd`). There are two differences:

- The torus projection is the published actual Reynolds unit.
- The irreducible self-dual Steinberg square and Schur's lemma are replaced by
  the irreducible-first-factor tensor adapter, which yields the scalar `1`
  directly.
