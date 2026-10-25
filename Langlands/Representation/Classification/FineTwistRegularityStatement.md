# Regularity of actual fine real twists

Author: Worker 166.

`Langlands.FineTwistRegularityStatement` is a closed proposition definition
combining three preservation statements for actual product-Levi
representations with the specialization needed by relative Jacquet comparison.
This pair states the interface; it contains no proof of the assertions.

## Product-Levi preservation clauses

For every prime `p`, p-adic field `F`, compatible topological datum `T`,
rank `n`, ordered block shape `B`, complex module `V`, actual representation
`ρ` of `B.Levi F.Carrier`, and arbitrary real vector `s`, the three named
propositions assert:

* `LeviRealPowerCuspidalityStatement`: the actual twist
  `T.leviRealPowerTwist B s ρ` is cuspidal if and only if `ρ` is cuspidal.
* `LeviRealPowerAdmissibilityStatement`: that twist is admissible if and
  only if `ρ` is admissible.
* `LeviRealPowerIrreducibilityStatement`: that twist is irreducible if and
  only if `ρ` is irreducible.

The first two use exactly the topology supplied by `T`.
`CuspidalSupport.IsLeviCuspidal` means admissibility together with vanishing
of the actual unipotent coinvariant quotient for every proper standard
block refinement. Admissibility includes smoothness and finite-dimensional
fixed spaces for every open subgroup. Irreducibility is the existing
simple-order predicate on actual subrepresentations.

The twist acts on the original carrier by the product of the positive real
characters `|det(m_i)|_F^(s_i)`, embedded in the complex units. The absolute
value is the published residue-normalized absolute value. No external
tensor decomposition or character-existence datum is supplied.

## Fine specialization

`FineTwistIrreducibleAdmissibleStatement` quantifies over every refinement
`S` of `B` and an irreducible cuspidal actual representation `ω` of the
flattened product Levi `(B.flatten S).Levi F.Carrier`. For arbitrary fine
and coarse real vectors `v₀` and `t`, put

```text
s(k) = -v₀(k) + t(((B.flattenBlockEquiv S).symm k).1).
```

The statement concludes irreducibility and admissibility of the existing
`RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t`, an actual
representation of `Geometric.refinedLevi F.Carrier B S`. Its action is the
flattened twist pulled back along the inverse of the constructed
`flattenedLeviEquiv`. The conclusion also explicitly retains cuspidality
of the flattened twist `T.leviRealPowerTwist (B.flatten S) s ω.ρ`.

Every clause preserves independent field and carrier universes `uF` and
`uV`. Every rank, including zero, is allowed. No unitarity, genericity,
chamber condition, parameter regularity, finite-length hypothesis, or
finite-dimensionality of the whole carrier is imposed.

## Internal provenance and proof obligations

This is an internal specialization of published constructions and transport
lemmas, rather than a new assertion attributed to an external source.
The statement imports the existing `RelativeJacquetMultiplicityStatement`
module to use its exact fine twist and all its underlying definitions.
It does not alter that module or its imports.

A later proof can use `Twist.LeviRealPower` for the open character kernel,
`Twist.AdmissibilityProof.isAdmissible_twist_iff` for admissibility, and
`Twist.SubquotientProof.isIrreducible_twist_iff` for irreducibility.
For cuspidality, each component of a refined unipotent element has
determinant one. The real character is therefore trivial on that actual
radical; `Jacquet.subsingleton_coinvariants_twist_iff` from
`Classification.SupercuspidalTwist` then identifies the vanishing predicates.
These assertions still need to be assembled into a proof of this statement.

For the fine specialization, the published continuous equivalence in
`Geometric.FlattenedLevi` and the existing admissibility and irreducibility
pullback lemmas transport the two properties to the actual refined subgroup.
Cuspidality in the final conjunct remains on the flattened product Levi;
no new cuspidality predicate on the refined subgroup is introduced.

This statement does not establish constituent extraction, opposite
reciprocity, induction regularity, Jacquet multiplicities, or an
irreducible head. Independent acceptance and publication of the statement
must precede its exact proof submission.
