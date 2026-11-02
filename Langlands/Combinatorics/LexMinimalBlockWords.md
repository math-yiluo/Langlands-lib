# Decreasing blocks in a least concatenated word

Authors: Worker 320 (shared Lean proof and initial explanation), Worker 438
(verification and expanded explanation).

These internal combinatorial lemmas support the proposed extraction of special
segment constituents from a least actual cuspidal Jacquet word. They are derived
from elementary list permutation and order properties, with no representation
theory or classification input.

`eq_or_lex_of_perm_decreasing` works over any linear order. A weakly decreasing
list is lexicographically greatest among its permutations. Induction on that
list handles the empty case by permutation with the empty list. In the nonempty
case the first entry of the permuted list occurs in the reference list and is
therefore at most its first entry. A strict inequality gives the lexicographic
comparison immediately. Equal first entries cancel from the permutation, and
induction gives either equality or comparison of the tails.

`lex_append_of_length_eq` proves that strict lexicographic comparison of lists
of equal length survives appending arbitrary suffixes. Induction on the
lexicographic proof excludes its proper-prefix case using the length equality,
preserves a strict comparison of the heads, and cancels equal heads.

`eq_blocks_of_minimal_flatten` assumes `List.Forall₂ List.Perm vs ss`, that every
reference block in `ss` is weakly decreasing, and that `vs.flatten` is not
strictly smaller than `ss.flatten`. Induction on the block pairing first applies
the single-block comparison. Equal initial blocks reduce the condition to the
tails, since a common prefix preserves strict lexicographic comparison.
Unequal blocks give a strict comparison which survives the remaining suffixes
because permutation gives equal block lengths, contradicting the condition.
Thus the complete lists of blocks are equal.

Empty blocks and repeated entries are permitted. The hypotheses concern the
individual block permutations and a comparison of the two flattened words;
no global sorting condition on the reference concatenation is needed.
