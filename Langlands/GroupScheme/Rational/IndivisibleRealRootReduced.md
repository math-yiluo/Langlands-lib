# Reducedness from the absence of double roots

This internal derived lemma supports the indivisible-root clause of Renard V.3.7
in `RelativeRealCorootStatement`. It applies to any finite crystallographic real
root pairing whose root set contains no double of a root.

For a dependent pair of roots, Mathlib gives integral Cartan entries whose
product is four. Their absolute values are bounded by four, so the entries have
the possibilities ±1, ±2, and ±4. The two entries equal to two identify the
roots; the two entries equal to minus two identify them up to sign. The four
remaining cases give a root equal to plus or minus twice another root. Positive
doubles contradict the hypothesis, and negative doubles reduce to positive
doubles by the negative root supplied by a self-reflection.

The proof uses the published Mathlib pairing identities and integer arithmetic.
It asserts no new original-source result and does not assume reducedness.
