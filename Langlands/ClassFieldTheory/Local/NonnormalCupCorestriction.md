# Cup, corestriction and norms for nonnormal middle fields

This internal support unit removes an unnecessary middle-field Galois
assumption from the existing degree-zero norm comparison and the resulting
abelianization cup comparison. All fields lie in the same arbitrary
universe. The actual subgroup, Tate corestriction, norm quotient, cup map
and Galois abelianization remain the published constructions.

For fields in a compatible tower `K ⊆ L ⊆ M`, assume first only that
`M/K` is normal. `relativeGaloisEmbedding` restricts an automorphism
of `M/K` to `L` and embeds its values into `AlgebraicClosure M`.
`relativeGaloisEmbedding_eq_iff` proves that two such embeddings agree
exactly when the quotient of their automorphisms belongs to the actual
subgroup `relativeGaloisSubgroup K L M`, the image of `Gal(M/L)` under
scalar restriction. Both directions explicitly use the fixing condition
on embedded elements of `L`.

With `M/L` finite dimensional, every embedding of `L/K` into the
algebraic closure extends to an embedding of `M/K`. Normality identifies
the latter embedding with an automorphism of `M/K`.
`relativeGaloisCosetEmbeddingEquiv` therefore constructs a bijection

```
Gal(M/K) / relativeGaloisSubgroup K L M
  ≃ (L →ₐ[K] AlgebraicClosure M).
```

Its value on a represented coset is the preceding restriction.
No normality of `L/K` is needed.

For the norm comparison, assume all three field extensions in the tower
are finite dimensional and `M/K` is Galois.
`relativeCosetNorm_baseUnit_nonnormal` proves that the actual Tate
coset norm of the embedded invariant unit `a : Lˣ` equals the embedded
field norm `normUnits K L a`. After applying the injective algebra map
from `M` into its algebraic closure, the additive coset sum becomes a
product. Reindex it by `relativeGaloisCosetEmbeddingEquiv`. Its factors
are exactly all the embeddings of `a`; separability of `L/K` follows
from the Galois upper extension. The determinant norm product formula
and scalar-tower compatibility give the asserted identity.

Now also assume `M/L` is Galois. The published degree-zero representative
formulas and subgroup reindexing yield
`relativeTateCorestriction_zeroClass_nonnormal`: corestriction of the
class of a middle-field unit is the class of its norm. Surjectivity of
degree-zero invariant-unit classes then gives
`tateZeroEquivNormQuotient_corestriction_nonnormal`, identifying actual
degree-zero Tate corestriction with `normQuotientTowerNorm K L M`.

Finally, supply raw invariant homomorphisms for `M/K` and `M/L`,
positively normalized fundamental classes `c` and `d`, and
`FundamentalClassTateCorestriction K L M` for these invariant maps.
`abelianizationCupToNormQuotient_corestriction_nonnormal` proves

```
cup_c (relativeAbelianizationInclusion K L M x)
  = normQuotientTowerNorm K L M (cup_d x).
```

Here the formula is in additive notation on the actual Galois
abelianizations and norm quotients. The proof represents `x` in
integral Tate degree minus two, uses the existing identification of
corestriction with subgroup inclusion, applies the supplied fundamental
cup/corestriction law, and uses the new degree-zero norm comparison.
It assumes neither cup bijectivity nor an Artin comparison.

This is derived content: the coset/embedding bijection and norm
calculation fill the missing nonnormal case, and the remaining steps
specialize published representative and projection formulas. The unit
does not modify the existing Galois-middle-field comparison. The general
finite Artin/cup comparison and the unconditional common-closure
existence theorem remain separate obligations.
