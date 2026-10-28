# Generic fine-twist Weyl self-association counts

Author: Worker 166.

`Langlands.GLRelativeGenericWeylCountStatement.{uF, uV}` is an internal
derived proposition definition. It states support containment and the resulting
finite-cardinality equality for actual minimal self-associating permutations.
This file supplies a statement; a separate proof must establish it.

For every prime `p`, `PadicField.{uF} p` and compatible `TopologicalData T`,
positive rank `n`, coarse block shape `B` and actual refinement `S`, set
`C = B.flatten S`. Let `omega` be a representation of the actual fine Levi
`C.Levi F.Carrier` on a complex module `V : Type uV`. Assume exactly that
`omega` is irreducible, admissible and unitarizable. The field and carrier
universes remain independent.

For arbitrary fine real vector `v0` and coarse real vector `t`, assume the
existing predicate `IsRelativeGenericParameter C B v0 t`. The actual twist is

```text
sigma = T.leviRealPowerTwist C
  (fun k => -v0(k) + t(((B.flattenBlockEquiv S).symm k).1)) omega.
```

The proposition asserts both:

1. Every `w : CuspidalSupport.AssociatingPermutations C C sigma sigma`
   has underlying permutation `w.val.val.val` in `Geometric.blockWeyl B`.
2. The subtype of these same self-associations satisfying that membership has
   the same `Nat.card` as the entire self-association type.

`AssociatingPermutations` retains the existing minimal representative,
actual full-Levi conjugation, and actual transported representation equivalence
witnesses. The restriction adds only the coarse Weyl membership predicate.
Both types are finite as subtypes of the finite coordinate permutation group;
the equality concerns actual natural-number cardinalities, including any
empty case. No alternate Weyl representative, quotient or counting definition
is introduced.

The proposition has no cuspidality, chamber, positivity, additional support
certificate or stabilizer assumption. It asserts no Jacquet multiplicity
formula, constituentwise comparison, quotient criterion or head consequence.
Those require separate representation-theoretic results.

## Derived provenance

This is a direct finite-set consequence of the third conjunct of the published
`Langlands.GLUnitaryWeylRealExponentRigidityStatement`, proved by
`Langlands.glUnitaryWeylRealExponentRigidity` in
[UnitaryWeylRigidityProof](UnitaryWeylRigidityProof.md). That conjunct applies
to every actual full-Levi self-conjugation and equivalence of exactly the twist
above, without a minimality premise. Apply it to each existing minimal
self-association witness. The first assertion follows. Inserting that
membership proof and forgetting it gives mutually inverse maps between the
restricted subtype and the original type. `Nat.card_congr` then yields the
second assertion.

The normalization and original-source motivation of the rigidity theorem are
recorded in [its statement](UnitaryWeylRigidityStatement.md). The present
proposition is an internal consequence of that Library result, rather than a
claim that an external source states this exact subtype equality. It imports
the published statement and the Mathlib finite-cardinality interface, without
editing any existing Library pair. The proof successor will import the
published rigidity proof and prove this exact proposition separately.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). Compilation and
proposition inspection are development checks; independent semantic review
and Library publication remain separate requirements.
