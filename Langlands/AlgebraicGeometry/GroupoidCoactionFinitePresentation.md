# Finite projective relation tensor presentations

For a `RingEtaleEquivalenceRelation t` with object ring `B` and relation ring `C`,
assume that `C` is a finite projective module over `B` through each of the source
map `s = algebraMap B C` and the target map `t`. Put
`A = GroupoidCoaction.invariantRing t`, the unchanged subring of elements for
which `t b = s b`. Both rings may lie in any common universe.

`finiteProjective_invariantRing_quotient` proves that `B` is finite, projective,
and faithfully flat over `A`. It also proves that the square with two copies of
the inclusion `A → B` and bottom maps `s, t : B → C` is a pushout in
`CommRingCat`. Target finiteness and projectivity are explicit arguments using
`t.toAlgebra`; source finiteness and projectivity use the given `B`-algebra
structure on `C`.

The proof specializes the published
`FiniteLocallyFreeQuotient.invariantRingQuotient`. The supporting lemma
`range_sup_eq_top` rewrites the relation's algebra generation hypothesis as
`s.range ⊔ t.range = ⊤`, using the subring description of algebraic adjunction.
`source_target_equivalence` reorders the relation's reflexivity, symmetry, and
transitivity witnesses into the convention required by that quotient theorem.
The invariant inclusion is injective because it is a subring inclusion, and its
range is exactly the equalizer of the source and target maps. Thus the quotient
and faithful flatness conclusions are proved from the finite projective
hypotheses; no quotient or descent conclusion is assumed.

`finiteProjectiveTensorEquiv` compares this pushout with the canonical tensor
product pushout to construct
`C ≃ₐ[B] B ⊗[A] B`. Here the tensor product has its usual `B`-algebra structure
through its first factor. The two coefficient lemmas prove the formulas
`s b ↦ b ⊗ 1` and `t b ↦ 1 ⊗ b`; the source formula also establishes that the
ring equivalence is a `B`-algebra equivalence. Both formulas come from the
compatibility of the pushout comparison isomorphism with its two legs.

This is a derived interface adapter for an existing Library quotient theorem
and Mathlib's tensor product pushout. It introduces no replacement definitions
of relations, coactions, or invariants, and does not assert the task's nonzero
invariant theorem. The published quotient theorem retains its own literature
provenance in its paired Markdown; this adapter makes no additional claim
about an external source.
