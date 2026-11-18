# Proof of the character theorem for split reductive groups

Author: Worker 902.

This module proves the statement
[`Rational.SplitRepresentationCharacterStatement`](SplitRepresentationCharacterStatement.md)
(Milne, *Algebraic Groups* (2017), Theorem 22.38) as the theorem

```text
Langlands.GroupScheme.splitRepresentationCharacterStatement :
  SplitRepresentationCharacterStatement.{u}
```

The theorem's type is exactly the published proposition and adds no hypotheses. `k` is
an arbitrary field, `G` an affine group scheme over `Spec k` and `p : SplitPinning G` a
split pinning. The statement says three things about the character
`lam ↦ dim ρ_lam` of a representation `ρ`:

1. it has finite support and is invariant under the reflections of the root datum;
2. two semisimple representations with the same character are isomorphic;
3. every finitely supported, reflection-invariant integer function on the character
   lattice is the difference of the characters of two representations.

## The proof

The proof is one line. It applies the reduction

```text
splitRepresentationCharacterStatement_of_classification :
  SplitHighestWeightClassificationStatement.{u} → SplitRepresentationCharacterStatement.{u}
```

from [`Rational.SplitRepresentationCharacterReduction`](SplitRepresentationCharacterReduction.md)
to the Library's proof `Langlands.GroupScheme.splitHighestWeightClassification` of the
fundamental theorem of highest weight (module
[`Rational.SplitHighestWeightClassificationProof`](SplitHighestWeightClassificationProof.md)).
That proof also holds over any field with no extra hypotheses.

## Helper modules in this contribution

- [`MatrixRepresentation.OperatorModule`](../MatrixRepresentation/OperatorModule.md):
  a matrix representation as a module over the free algebra of its coefficient operators.
  Stable subspaces are exactly the submodules, intertwiners are exactly the module maps,
  and irreducible and semisimple representations are exactly the simple and semisimple
  modules. Direct sums of representations match products of modules.
- [`Rational.SplitWeightModule`](SplitWeightModule.md): weight spaces of such modules for
  the split torus. They agree with the Library's `representationWeightSpace`, are
  preserved by module isomorphisms, and their dimensions add over complementary
  submodules.
- [`Rational.SplitRepresentationCharacterReduction`](SplitRepresentationCharacterReduction.md):
  the reduction above. Conjunct 1 is unconditional. Conjunct 2 is proved by strong
  induction on the dimension, splitting off a simple summand of maximal highest weight;
  it uses conjuncts 2 and 3 of the classification. Conjunct 3 is proved by
  triangularity of the characters of the simple representations against dominant
  weights; it uses conjunct 1 of the classification.

The Markdown files of the helper modules explain those proofs in detail.
