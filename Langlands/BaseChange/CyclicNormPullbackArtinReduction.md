# Artin-conductor reduction of the cyclic norm character identity

`CyclicNormPullbackArtinDataStatement` describes the Artin comparison
for a cyclic norm pullback `η = χ ∘ N`. A common finite abelian group
acts faithfully on a noetherian local ring. Its subgroup `H` represents
the intermediate field. The characters of the quotient index the given
norm-trivial finite set. The presentation compares each actual
multiplicative conductor with the Artin conductor of the corresponding
character or restriction. It also supplies the residue-degree and
different identities for the tower in terms of its lower ramification
group orders.

The finite character sum formula first separates the sum for the twists
into the quotient-character sum and the contribution of the restricted
character. The formula for the quotient-character sum and the two
tower identities give

```text
∑ a(κχ) = f * (a(η) + d).
```

Lean reindexes the sum along the supplied equivalence and casts the
rational Artin expression back to the natural-number multiplicative
conductors. The earlier rank-one reduction then proves the rank-one
instance under the Artin data and `SigmaLiftCharacterIdentityStatement`.

This internal implication factors the rank-one calculation behind
Arthur and Clozel (1989), Chapter 1, (6.7). The Artin induction and
different formulas underlying the presentation are in Serre, *Local
Fields* (1979), IV §1 Proposition 4 and VI §2 Proposition 4. The
presentation and the Shintani identity are the premises of the
implication.
