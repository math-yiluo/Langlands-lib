# Product-Levi cuspidal localization

Authors: Worker 379 and Worker 276, with three lemmas by Worker 954 (see the
helper module below).

The module `Langlands.Representation.Exponents.ProductLeviCuspidalLocalizationProof`,
namespace `Langlands.ProductLeviCuspidalLocalization`, proves the published
statement `Langlands.GLProductLeviCuspidalLocalizationStatement` of
`Langlands.Representation.Exponents.WeylBranchPiecesStatement`.

## Main result

`glProductLeviCuspidalLocalization` has exactly the type

```
GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM}
```

for independent universes `uF` (the p-adic field), `uV` (the irreducible
Levi-cuspidal representation `ρ`) and `uM` (the middle representation `σ`). It
has no further hypotheses.

In words: fix a prime `p`, a finite extension `F` of `ℚ_p` with its topology,
a positive rank `n`, a block shape `B` of `n`, a refinement `Q` of `B` with
`D = B.flatten Q`, and a smooth complex representation `σ` of the Levi of `D`.
Let `S'` be a refinement of `B`, and let `ρ` be an irreducible Levi-cuspidal
representation of the Levi of `B.flatten S'`. Suppose `ρ` is a subquotient of
the flattened inner opposite Jacquet module along `S'` of the middle normalized
induction `middleInduced T B Q σ`. Then there are `g ∈ blockWeyl B`, a refinement
`R'` of `D` and a proof that `g` conjugates the Levi of `D.flatten R'` onto the
Levi of `B.flatten S'`, such that `g` is a minimal representative for
`(D, B.flatten S')` and `ρ` is a subquotient of the transport by `g` of the
flattened inner opposite Jacquet module of `σ` along `R'`.

## Proof

The proof is one application:

```
productLeviCuspidalLocalization_of_geometricLemma
  Geometric.padicProductLeviGeometricLemma.{uF, uM}
```

- `Geometric.padicProductLeviGeometricLemma` is the published proof, in
  `Langlands.Representation.Geometric.ProductLeviGeometricLemmaProof`, of
  `Geometric.PadicProductLeviGeometricLemmaTheorem`. That statement is
  Bernstein–Zelevinsky's normalized geometric lemma (BZ77, 2.12) for the group
  `B.Levi`, with pieces indexed by the minimal representatives in `blockWeyl B`.
  It is used at universes `uF` and `uM`, so its inducing carriers live in the
  universe of `σ`.
- `productLeviCuspidalLocalization_of_geometricLemma` is the conditional
  derivation in the helper module
  `Langlands.Representation.Exponents.ProductLeviCuspidalLocalizationConditional`
  (Worker 276, file `ProductLeviCuspidalLocalizationConditional.md` explains it
  in detail). It shows that this geometric lemma implies the target statement.
  In outline: it reverses the inner refinement `S'` so that the inner opposite
  Jacquet module becomes a transported upper one; it applies the geometric lemma
  to the actual composite `innerJacquetInductionFunctor`, whose gluing gives a
  piece containing `ρ` as a subquotient; it rules out the pieces that are proper
  normalized inductions, because a quasicuspidal irreducible representation is
  not a subquotient of a proper induction (BZ77, 2.4(d), via
  `CuspidalSupport.padicProperRefinedInduction`); it identifies the remaining
  whole-Levi piece with a transported upper Jacquet module of `σ`; and it undoes
  the two reversals, checking that the resulting permutation lies in
  `blockWeyl B` and is a minimal representative.

## Files

- `Langlands/Representation/Exponents/ProductLeviCuspidalLocalizationProof.lean`
  and `.md` (this pair): the closing theorem.
- `Langlands/Representation/Exponents/ProductLeviCuspidalLocalizationConditional.lean`
  and `.md`: the conditional derivation, unchanged from Worker 276's shared
  draft (revision 2 of task `8ece4423`).

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`. There
is no `sorry` and no new axiom.
