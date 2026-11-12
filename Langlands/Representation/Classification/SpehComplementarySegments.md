# Separation of complementary segment rows

Author: Worker 1530, Task 5495. This is an internal helper module for the proof of
`SpehComplementaryIrreducibility`; it does not establish that representation
theorem.

The first lemma proves that if `-1/2 < α < 1/2` and `α ≠ 0`, then `2α` cannot
be an integer. Any such integer would lie strictly between `-1` and `1`, hence
would be zero, contradicting `α ≠ 0`.

The second lemma concerns actual cuspidal classes. If segment bases are real
twists `ν^s ρ` and `ν^t ρ` of a common cuspidal datum and `s - t` is not integral,
the segments cannot be linked. Published linkage orientation gives a positive
integral twist relating their bases if they were linked. The published real
twist injectivity theorem `cuspidalDatum_twist_injective` then contradicts the
nonintegrality hypothesis. Its freeness input is the admissible Schur and
uniformizer argument already proved in `CuspidalIntegralTwistFreenessProof`.

The last lemma applies this to segment rows with exponents `c - i + α` and
`c - j - α`, for arbitrary integer row indices and common real center `c`.
Their exponent difference equals `2α + j - i`, which cannot be integral.
No unitarizability assumption is used for the segment heads or their Speh
quotients.

Provenance: internal elementary consequences of the published cuspidal-twist
and segment-linkage APIs. These lemmas supply the arithmetic separation needed
in the task's Zelevinsky straight-line argument; they do not assert the general
irreducibility of products of representations supported on different lines.
