# Scalar cup of a cyclic carry class

This internal calculation uses the published positive carry class and the
actual degree-minus-two Tate cup map. Let `K : Type v` and `L : Type u`
be fields with a `K`-algebra structure, and let `n` be a nonzero natural
number. The universes of the two fields are independent. The normalized
cocycle construction only needs a character into `Multiplicative (ZMod n)`.
The inverse-row evaluation requires a group isomorphism
`χ : Gal(L/K) ≃* Multiplicative (ZMod n)` and a finite enumeration of the
Galois group. The final cup formulas assume that `L/K` is finite Galois.
No local-field, cup-bijectivity or reciprocity assumption occurs here.

`sum_cyclicCarry` proves that the sum of `cyclicCarry x b` over all
`x : ZMod n` equals `b.val`. Sum the published identity
`n * cyclicCarry x b + (x+b).val = x.val + b.val` over `x`.
Translation by `b` permutes `ZMod n`, so the two sums of representatives
cancel. Positivity of `n` cancels its remaining factor. This also covers
`n = 1`.

`normalizedCyclicCocycle K L χ a` applies the published
`normalizedRepresentative` construction to `cyclicUnitCocycle K L χ a`.
Its value at `(1,1)` is zero in additive notation. Consequently the
normalization changes no value: its additive value at `(g,h)` is
`cyclicCarry (χ g).toAdd (χ h).toAdd • baseUnit K L a`.
`normalizedCyclicCocycle_class` identifies its ordinary cohomology class
with the original `cyclicClass`.

For an isomorphism `χ`, reindexing the inverse-row sum by `χ` and using
`sum_cyclicCarry` gives

```
inverseRowSum (normalizedCyclicCocycle K L χ.toMonoidHom a) g
  = (χ g⁻¹).toAdd.val • baseUnit K L a.
```

The generic theorem `scalarH2Cup_minusTwoClass` identifies cup on the
single-chain generator at `g` with the degree-zero class of this actual
invariant sum. The published `integralTateMinusTwoEquiv_class` sends that
single-chain class to `Abelianization.of g`. The invariant sum is the
embedded base unit `a ^ (χ g⁻¹).toAdd.val`; the published comparison
`tateZeroEquivNormQuotient_zeroClass` sends its Tate class to its actual
field-norm class. Thus `abelianizationCupToNormQuotient_cyclicClass` proves

```
abelianizationCupToNormQuotient K L (cyclicClass K L χ.toMonoidHom a)
    (Additive.ofMul (Abelianization.of g))
  = (χ g⁻¹).toAdd.val • Additive.ofMul (normQuotientProjection K L a).
```

`normQuotientProjection_degree_nsmul` proves that `[L:K]` annihilates
the norm class of every base unit: the norm of the included unit `a` is
`a ^ [L:K]`. This lemma only requires a finite field extension.
`inverse_val_nsmul_eq_neg` proves in any additive commutative group that
`(-z).val • b = -(z.val • b)` whenever `n • b = 0`.
The field degree is `n`, by the Galois automorphism count and `χ`.
Using these facts yields the signed formula
`abelianizationCupToNormQuotient_cyclicClass_signed`:

```
abelianizationCupToNormQuotient K L (cyclicClass K L χ.toMonoidHom a)
    (Additive.ofMul (Abelianization.of g))
  = -((χ g).toAdd.val • Additive.ofMul (normQuotientProjection K L a)).
```

The sign follows from the inverse in the proved generic representative
formula and the inverse-action first-homology convention. This module
derives its results from published constructions and elementary finite
sums; it does not change the carry, Tate, or abelianization conventions.
It supplies a focused prerequisite for the local reciprocity task.
The cyclic Artin comparison, passage to general finite Galois groups,
and the unconditional common-closure existence theorem remain separate
obligations.
