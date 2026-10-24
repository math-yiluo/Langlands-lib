# Integral away comparison compatible with a supplied full comparison

Author: Worker 18.

`Langlands.Global.PrimeToIntegralProfiniteIntegerAdeleComparisons` is a
no-parameter definition with type `Prop`. It states the integral residue-to-adele
comparison away from every natural modulus, relative to a supplied normalized
full comparison. This module states the proposition; it does not prove it or
construct an unconditional comparison.

## Hypotheses and conclusion

The proposition universally quantifies a ring equivalence
`eFull : ProfiniteIntegerRing ≃+* integralFiniteAdeles ℚ`, continuity of
`eFull` and `eFull.symm`, and the normalization

```text
∀ z : ℤ,
  (eFull (ProfiniteIntegerRing.intCastHom z) : FiniteAdeles ℚ) =
    algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ).
```

For each `m : ℕ`, it then requires a ring equivalence
`e₀ : PrimeToProfiniteIntegerRing m ≃+* primeToIntegralFiniteAdeles m`
with the following four properties:

1. `Continuous e₀`.
2. `Continuous e₀.symm`.
3. For every integer `z`, the underlying away adele of
   `e₀ (PrimeToProfiniteIntegerRing.intCastHom m z)` equals
   `algebraMap ℚ (PrimeToFiniteAdeles m) (z : ℚ)`.
4. For every `a : ProfiniteIntegerRing`,
   `e₀ (PrimeToProfiniteIntegerRing.restrict m a) =
   primeToIntegralRestriction m (eFull a)`.

The last equality is in the integral away subring and uses exactly the supplied
`eFull`. No new full equivalence is chosen. The continuity and normalization
assumptions are internal to the proposition, so its declaration itself has no
parameters.

## Existing models and all natural moduli

The source rings and their integer maps and restriction are imported from
[`ProfiniteIntegerRing`](ProfiniteIntegerRing.md). The full ring is the inverse
limit of `ZMod n` over positive integers with divisibility reduction maps. The
away ring retains the positive moduli coprime to `m`. Both use their subspace
topologies from the products of discrete residue rings.

The targets, diagonal rational maps, and integral restriction are imported from
[`PrimeToFiniteAdeles`](PrimeToFiniteAdeles.md) and its published dependencies.
`FiniteAdeles ℚ` is the actual restricted product over finite places of `ℚ`;
`PrimeToFiniteAdeles m` retains the finite places whose prime ideal does not
contain `(m : 𝓞 ℚ)`. Each integral subring consists of the elements integral
at every retained place and has the subspace topology from that restricted
product. These are the published rings and topologies, with no replacement
adelic model.

All natural numbers `m` are included, with no primality, positivity, or
nontriviality assumption. At `m = 1`, every positive residue modulus and every
finite place is retained. At `m = 0`, the only coprime positive residue modulus
is one, and there are no retained finite places; the corresponding away rings
are trivial. The statement does not impose a rational tensor comparison.

## Internal provenance and use

This is an internal prerequisite extracted from the integral clauses of
`Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparisons`, defined in
[`PrimeToRationalProfiniteIntegerComparison`](PrimeToRationalProfiniteIntegerComparison.md).
It is not presented as a theorem quoted from external literature.

The published rational away target takes
`h : RationalProfiniteIntegerAdeleComparison` and uses its coupled full
witnesses `h.choose` for the integral comparison and
`h.choose_spec.2.2.2.choose` for the rational comparison. This prerequisite
requires only the full integral witness and its own continuity and integer
normalization hypotheses. A proof of this prerequisite can therefore be applied
to exactly `h.choose` and its existing properties. Retaining that supplied
witness in the restriction equation preserves the compatibility needed by the
parent rational construction.

Quantifying over every such `eFull` is deliberate: replacing it with a newly
chosen full comparison would leave an additional comparison-uniqueness
obligation before the parent's coupled rational witness could be used. The
present statement isolates this integral descent obligation; its proof and the
parent's rational tensor construction remain separate work.
