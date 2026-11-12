# Cyclic inverse cup and positive carry symbols

This internal construction compares the actual degree-minus-two inverse cup
map with the published finite carry symbol. The general algebraic lemmas
allow independent universes for the base and extension fields. The local
comparison uses a p-adic field `F` and a finite Galois extension `D/F` in
the same arbitrary universe. It assumes an actual class `c`, its positive
fundamental-class normalization under `FiniteArtinSymbol.relInv`, and
bijectivity of its actual Tate cup map in degree minus two. No comparison
between cup and Artin symbols is assumed.

`geometricCupCharacter` is the homomorphism on the actual norm quotient
obtained by composing geometric inverse cup with the abelianization lift
of a supplied character. It is defined for any finite Galois extension
and any character into a nonzero cyclic modulus.

`cyclicClass_eq_neg_nsmul_of_cup` uses a cyclic coordinate
`χ : Gal(L/K) ≃* Multiplicative (ZMod n)`. If cup with `c` on
`Abelianization.of g` is the norm class of a unit `a`, it proves

```
cyclicClass K L χ.toMonoidHom a = -((χ g).toAdd.val • c).
```

The published surjectivity of cyclic carry classes writes `c` as the
carry class of another unit `b`. The cyclic H2-to-norm equivalence sends
the carry classes of `a` and `b` to their respective norm classes.
Apply its injectivity and the signed cup formula from
`CyclicCupEvaluation` to obtain the displayed equality.

`denominatorEquiv_eq_val_nsmul` expresses the image of a residue `z`
in `Q/Z` as `z.val` times the positive reciprocal class.
For a coordinate whose modulus is `[D:F]`,
`symbolValue_cyclicCoordinate_of_cup` applies the relative invariant
to the preceding carry-class equality. The positive fundamental-class
normalization and the denominator equivalence identify the symbol
with `-(χ g).toAdd`.

To evaluate inverse cup, represent its value in the actual Galois
abelianization by `Abelianization.of g` and use
`cup_arithmeticReciprocityOfCup`. Consequently
`arithmeticReciprocityOfCup_character_cyclicCoordinate` proves that
the character value of arithmetic inverse cup is the multiplicative
form of the negative carry symbol. Output inversion gives
`geometricReciprocityOfCup_character_cyclicCoordinate`, with the
positive symbol.

`cyclicCoordinateGenerator_pow_val` shows that every group element is
the coordinate generator raised to its coordinate representative.
`character_eq_pow_cyclicCoordinate` then writes every character into
the same cyclic modulus as a natural power of the coordinate;
the exponent is its value at the coordinate generator. The carry
class and its symbol respect these powers, by
`cyclicClass_pow_character` and `symbolValue_pow_character`.
The abelianization lift also respects powers. Thus
`geometricReciprocityOfCup_character_of_cyclicCoordinate` proves the
positive comparison for every character into the degree modulus.

For any cyclic finite Galois group, the chosen cyclic-group equivalence
and the Galois automorphism count provide such a coordinate.
`geometricReciprocityOfCup_character_of_isCyclic` proves, for every
degree-modulus character `ψ` and base unit `a`,

```
Abelianization.lift ψ
    (geometricReciprocityOfCup F.Carrier D c h
      (normQuotientProjection F.Carrier D a))
  = Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a).
```

`geometricCupCharacter_projection_of_isCyclic` states the same
representative formula for the constructed homomorphism. All formulas
include degree one; no nontriviality hypothesis is used.

The construction and proofs derive from the existing carry algebra,
cyclic norm comparison, actual signed cup evaluation, and denominator
arithmetic. They preserve those conventions. This focused support unit
does not prove the comparison for general finite Galois groups, the
published arithmetic comparison premise, or the unconditional
common-closure reciprocity existence target.
