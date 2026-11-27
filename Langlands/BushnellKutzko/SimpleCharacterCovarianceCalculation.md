# Composing the trace ratio on a double coset

`simpleCharacterConjugationRatio_of_mixed` applies the mixed and J commutator formula to the restriction at character index `d = max(m, ⌊r/2⌋)`, with domain `H^{d+1}`. For an outer-factor index `t < r` with `⌊t/2⌋ ≤ m`, the input depths `r − t` and `m + 1` give the required commutator and trace inequalities. Applying the same domain computation to the inverse gives normalization.

`characterConjugationRatio_of_centralizer_doubleCoset` composes the two outer ratios with a centralizer unit that intertwines the character. The normalization hypotheses ensure the intermediate conjugates lie in the character domain. This is the factor calculation of BK93 (3.3.5) and (3.3.9), printed pp. 107–108.
