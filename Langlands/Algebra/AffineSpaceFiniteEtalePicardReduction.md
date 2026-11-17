# Picard triviality from a polynomial product decomposition

Author: Worker 573.

This internal reduction proves

```text
Langlands.Algebra.AffineSpaceFiniteEtalePolynomialProductStatement.{u} →
  Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement.{u}.
```

It imports the published Picard statement unchanged and retains the polynomial
product decomposition as an explicit hypothesis. It therefore does not yet
prove the unconditional target of Task 7538.

## Implemented proof

`Langlands.Algebra.subsingleton_pic_pi` proves triviality of the Picard group of
a finite product of commutative rings, assuming each factor's Picard group is
trivial. Give each factor its algebra structure over the product by the
evaluation ring homomorphism. The resulting map from the product into the
product of these algebras is the identity and hence bijective. The published
`subsingleton_pic_of_bijective_algebraMap_pi` then applies. This also handles
the empty product.

`Langlands.Algebra.subsingleton_pic_of_polynomial_product` applies this to
multivariate polynomial rings over fields. Mathlib's
`MvPolynomial.uniqueFactorizationMonoid` in
`Mathlib.RingTheory.Polynomial.UniqueFactorization` supplies unique
factorization. Mathlib's Picard-group instance for GCD domains makes the
Picard group of each factor subsingleton. The published
`subsingleton_pic_of_ringEquiv` transfers the conclusion back across the
given ring isomorphism. The ring, the family of coefficient fields, and
the index type have independent universes `u`, `v`, and `w`.

`Langlands.Algebra.affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct`
introduces the field, characteristic-zero instance, number of variables,
and finite étale polynomial algebra from the exact target. Apply the
decomposition hypothesis, install the resulting finite-index and field
instances, and invoke the preceding lemma.

## Provenance and scope

The proof is an internal algebraic reduction motivated by Conrad, *Reductive
group schemes* (2014), Remark 7.2.13, p.259. Its missing geometric input and
precise source comparison are in the paired documentation of
`AffineSpaceFiniteEtaleDecompositionStatement`.

The two Picard transport/product lemmas come from the published
`Langlands.Algebra.IntegerFiniteEtalePicard` of Worker 4699; they are
reused by Lean name. The proof introduces no assumptions about connectedness,
faithfulness, or nonzeroness of the covering ring. It covers zero variables
and an empty product. Characteristic zero is used only by the assumed
decomposition.
