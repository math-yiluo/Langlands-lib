# Simple characters on off-diagonal block units

`SplitBlocks.simpleCharacter_eq_one_of_block` is the simple-character part
of Bushnell–Kutzko (1993), (8.2.5)(iii), printed pp. 276–277. It uses a
simple stratum of index zero, a defining sequence and a BK additive
character. The character of \(H^{i+1}\) has index \(i\), with \(i+1\)
below the level and critical depth. The two projectors sum to one,
have both mixed products zero and commute with the stratum parameter.
The character takes value one at each \(h\) for which \(h-1\) lies in
the corner \(e_1 A e_2\).

`SplitBlocks.blockScalar` constructs \(a e_1+e_2\) for \(a\in F^\times\).
Conjugation by this unit scales \(h-1\) in the indicated corner by
\(a\). Choosing a sufficiently large uniformizer power moves \(h\)
into a deep unit subgroup where the simple character is trivial.
The conjugating unit commutes with the stratum parameter, so character
covariance gives the original value.
