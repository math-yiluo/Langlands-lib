# Truncated uniqueness of the polar-part identity

`Langlands.Henniart.polarPartTruncatedUniqueness` proves
`Langlands.Henniart.PolarPartTruncatedUniquenessStatement`. If the counting
identities hold for `T` at every positive rank `n` and exponent `j < n * e`,
then `T n s` equals `polarTwistCount q n s` throughout `s < n * e`.
[Published statement](HenniartPolarPart.md)

The result formalizes the \(f=1\) converse of Lemma 3.3 (`lem:polar`) in the
operator note *The numerical local Langlands correspondence for GL_n: counts
on the two sides and the recommended route of proof*, 16 November 2026
(registered source `operator-numerical-llc-route-2026-11-16`, §3, TeX lines
251–263, PDF p. 6). The truncation is the form used in part (b) of the proof of
Proposition 5.12 (`prop:LDcount`, TeX lines 832–847, PDF p. 22).

## The counting identity for the model

`sum_polarTwistCount` specializes `polarPartCountingIdentity` to \(f=1\).
The right-hand side becomes \((q-1)q^j\). The prime-power hypothesis gives
\(1\le q\), so the integer subtraction \(q-1\) is the cast of the natural
subtraction. Lean takes the equality back to \(\mathbb N\) and reindexes both
divisor sums by pairs \((d,m)\) with \(dm=n\). In the summand of rank \(d\), the
condition \(mk\le j\) is equivalent to \(nk\le dj\) by multiplication or
cancellation by the positive divisor \(d\). Casting the resulting identity to
`ℕ∞` gives the same total as the hypothesis on `T`.
[Counting identity proof](HenniartPolarPartCountingIdentityProof.md)

## Isolating the summand at \((n,s)\)

Lean uses strong induction on rank \(n\) and then on the Swan exponent \(s\).
In the cumulative identity at \(j=s\), it removes the summand indexed by
rank \(n\) from the outer sum. At rank \(n\), the inner index set is
\(\{0,\ldots,s\}\), so the last summand is the value at \((n,s)\).

Every term of smaller rank \(d\) in the remaining sum satisfies
\(nk\le ds<dne\), hence \(k<de\), so the rank induction hypothesis applies.
Terms of rank \(n\) with \(k<s\) are covered by the Swan exponent induction
hypothesis. This gives equality of the two remainders. The common remainder
is finite because it is bounded by the total \((q-1)q^s\) in `ℕ∞`.
Cancelling it leaves the asserted equality at \((n,s)\).
