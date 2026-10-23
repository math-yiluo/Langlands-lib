# Normalized residue-limit and p-adic product comparison

`Langlands.Global.ProfiniteIntegerPadicProductComparison` is a proposition
with no parameters or hypotheses. It asserts the existence of a ring
equivalence

\[
e:\mathrm{ProfiniteIntegerRing}\;\simeq\;
  \prod_{p\ \mathrm{prime}}\mathbb Z_p
\]

such that both \(e\) and \(e^{-1}\) are continuous and, for every integer \(z\)
and every prime \(p\),

\[
e(\mathrm{ProfiniteIntegerRing.intCastHom}(z))_p
  =(z:\mathbb Z_p).
\]

This file defines the proposition; it does not prove it or choose a witness.

## Rings and topologies

The source is exactly the existing `Langlands.Global.ProfiniteIntegerRing`,
the subring of \(\prod_{n>0}\mathbb Z/n\mathbb Z\) consisting of families
compatible under reduction whenever one positive modulus divides another.
Its operations are coordinatewise and its topology is the subspace topology
from the product of the finite discrete residue rings.
`ProfiniteIntegerRing.intCastHom` sends an integer to its compatible family
of residues.

The target is the dependent function type
`(p : Nat.Primes) → PadicInt (p : ℕ)`, with the standard pointwise ring
operations and the product of Mathlib's existing p-adic integer topologies.
`PadicInt p` is the subtype of `Padic p` consisting of elements of norm at
most one; its metric topology is inherited from the p-adic field.
The local instance `Fact p.val.Prime := ⟨p.property⟩` supplies primality
from each index. It introduces no assumption on the proposition and changes
neither ring nor topology.

The witness is a unital ring equivalence (`≃+*`).
`Continuous e` and `Continuous e.symm` refer to these existing topologies.
No topology is transported along the proposed equivalence.

## Normalization and provenance

The integer formula records the compatibility needed when this comparison
is composed with the product-to-integral-adele comparison: the canonical
residue family of \(z\) must become the diagonal family of the same integer
in every p-adic factor. For a unital ring equivalence this formula already
follows from preservation of integer casts, because `intCastHom` is the
canonical integer ring homomorphism. Including it explicitly makes the
required normalization available as part of the comparison interface; it
does not assert an additional choice or a uniqueness theorem.

This is an internal auxiliary statement for the rational profinite-integer
comparison project, derived from the existing residue-limit construction
and Mathlib's actual `PadicInt` rings. It is not attributed verbatim to a
literature source. The existing
`Langlands.Global.ProfiniteIntegerRing.toPadic` in
`Langlands.Global.ProfiniteIntegerPadicProjection` provides compatible,
continuous prime-power projections that a separate proof may use; those
projections alone do not establish the product equivalence.

The statement defines no replacement profinite ring, assumes no comparison
as a structure field, and includes no finite-adele or rational tensor
conclusion. Its proof is a separate task.
