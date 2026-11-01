# Regularity from finite projective dimension of the residue field

`Langlands.CommutativeAlgebra.ResidueFieldFiniteProjectiveDimensionRegularStatement.{u}`
is the proposition

```lean
∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
  (∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE
    (ModuleCat.of R (IsLocalRing.ResidueField R)) n) →
  IsRegularLocalRing R
```

It asserts that a Noetherian local commutative ring is regular if its residue
field has finite projective dimension as a module over that ring. The universe
`u` is arbitrary. The Lean file defines the proposition without proving it.

## Original source

This is precisely implication (1) to (3) of the Stacks Project, Proposition
10.110.5 ([Tag 00OC](https://stacks.math.columbia.edu/tag/00OC)). That proposition
equates finite projective dimension of the residue field, finite global
dimension of the ring, and regularity. Only the first-to-third implication is
stated here; neither its converse nor the equality of numerical dimensions is
part of this Lean proposition.

The retained original is `00OC.html` in registered directory source
`stacks-regular-local-homological-2026-11-01`, SHA-256
`21820755db776b97fc099941b898e15c3b34a12ac214b637216d74b85046b6fd`.
The complete page has been read, and it has no comments. There is no separate
project errata note for this source.

The source proof uses Lemmas 10.110.3 and 10.110.4 to compare the embedding
dimension with the Krull dimension. That is a description of the source proof,
not an implemented Lean argument or a required route for a subsequent proof.

## Lean conventions and scope

`IsLocalRing.ResidueField R` is the quotient of `R` by its unique maximal ideal,
with its canonical `R`-module structure. It is a type in the same universe as
`R`. `ModuleCat.of` supplies the corresponding categorical module object.
`CategoryTheory.HasProjectiveDimensionLE X n` is the categorical projective
dimension bound by a natural number. Existence of such an `n` is finite
projective dimension, including dimension zero.

`IsRegularLocalRing` is Mathlib's unchanged class: locality, Noetherianity, and
equality of the minimal number of generators of the maximal ideal with the
Krull dimension. Thus the conclusion has its usual commutative algebra
meaning. No domain, dimension, characteristic, completeness, henselianity or
excellence hypothesis is added. Finiteness of projective dimension is assumed
only for the residue field. There is no assumption about all finite modules or
about global dimension.

This proposition is a homological prerequisite for proving regularity of prime
localizations. It does not assume regularity of the original ring, factoriality,
or a Picard-group vanishing statement.
