# Chamber alignment in a finite rational root system

This internal derived algebraic unit concerns an arbitrary rational root pairing
`P : RootPairing J ℚ M N`. Roots need not be reduced or crystallographic.
`Regular P f` means that every root evaluates nontrivially at the covector `f`.
`SameChamber P f g` means that the positive root sets determined by `f` and `g`
agree.

The canonical form on the coweight space is the sum over all root indices of
the products of root evaluations. Its value on a coroot with itself is positive:
every summand is a square and the summand at that coroot's index is four.
Mathlib's canonical-form identity implies that twice its pairing with a coroot
equals that coroot's squared norm times the corresponding root evaluation.

When `J` is finite and `P.IsRootSystem`, the root indices determine a root-system
automorphism: its weight map is determined on the spanning roots and the weight
representation is faithful. Thus the automorphism group and Weyl group are
finite. Maximizing the canonical pairing of `f` with a Weyl translate of `g`
and comparing with every coreflection shows that every product of corresponding
root evaluations is nonnegative. This conclusion allows singular covectors.
The coweight maps reverse composition, so the comparison uses multiplication
of the maximizing Weyl element on the right by a generating reflection.

If both covectors are regular, regularity is preserved by the coweight map,
since root evaluations are permuted. The nonnegative products are therefore
positive. Each pair of evaluations has the same sign, proving the existence
of a Weyl translate in the same chamber. Empty root systems are allowed.

The proof uses the definitions and identities in Mathlib's root-pairing,
canonical bilinear form, Weyl group and finite-maximum modules. It is an
internal deduction from these algebraic inputs, with no new literature claim.
The elementary permutation finiteness argument also appears in the published
conditional group-scheme module `Rational.RootFiniteness`; this unit proves the
generic algebraic form without any group-scheme assumptions.

This supplies chamber alignment only. It proves neither intrinsic geometric
relative reflections nor triviality of the positive-system stabilizer in the
actual rational normalizer quotient. Those geometric obligations, quotient
generation and the unrestricted `RelativeRootSystemStatement` remain open.
