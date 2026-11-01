# Consecutive runs in a lexicographically minimal integer word

`Langlands.Combinatorics.LexMinimalConsecutiveRuns` is a proposition definition.
This module states the finite-word implication and supplies no proof.

Let `P` be a predicate on finite lists of integers. It must preserve each of
the following local moves in every fixed prefix `l` and suffix `r`:

1. Swap adjacent entries `a,b` whenever neither is the other plus one.
2. Replace `[b+1,b,b]` by `[b,b+1,b]`.
3. From `[b+1,b,b+1]`, obtain at least one of `[b+1,b+1,b]` and
   `[b,b+1,b+1]`.

Every occurrence of these displayed lists is inside the unchanged prefix and
suffix. Equal adjacent entries are permitted by the first condition, where
the move changes nothing. The third condition is a disjunction; it does not
assume that both resulting words belong to the family.

Suppose `P w` and no word satisfying `P` is strictly below `w` in the usual
lexicographic order on integer lists. The conclusion is a finite list of
pairs `(a,m)`, with `m > 0`, whose first coordinates are nondecreasing at
adjacent positions. Concatenating their lists
`[a,a-1,...,a-(m-1)]`, in order, gives exactly `w`.
Here `List.IsChain` records the adjacent weak inequalities; transitivity
also gives weak increase between any two ordered positions.
The empty word is allowed and can have the empty list of runs. No claim
of uniqueness, maximality, or existence of a least word in an arbitrary
family is part of the proposition.

## Provenance and intended application

This is a derived combinatorial abstraction of the argument of Jantzen
(2000), Lemma 2.2.2, printed pp.545-547 / PDF pp.7-9. The registered source
is `jantzen-2000-square-integrable-classical-i`, SHA256
`539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.
Its word entries are real exponents on a single translate of the integers.
Subtracting the fixed translate leaves integer offsets and preserves the
lexicographic comparisons and consecutive-step relations used here.
The present proposition separates that finite combinatorics from the
representation-theoretic realization of the local moves.

The source first excludes gaps greater than one by an adjacent interchange,
then uses the first triple move to exclude repeated lower endpoints.
For a repeated interior entry, it commutes that entry left past entries
differing by more than one, applies the second triple alternative, and
uses the first triple move at the preceding position. This yields a word
strictly below the original in either branch. Repeating the argument on
the suffix gives the ordered runs. The first lexicographic comparison
printed on p.545 has its direction reversed: the swapped word for
`alpha_2 < alpha_1-1` is below the original. The proposition uses that
correct direction. When no later entry reaches the current first entry,
the first run extends to the end of the word; the list formulation
includes this case.

The arbitrary predicate and its local closure properties are explicit
hypotheses, not conclusions about Jacquet modules. There is no finite
length, irreducibility, unitarity, or analytic hypothesis here.
An application must separately supply a lexicographically minimal actual
Jacquet constituent, its integer offsets, both repeated-factor transfers,
and the actual adjacent interchange for every required pair while retaining
all outside factors. This module gives none of those inputs. It also gives
no segment extraction, commutation of segment inductions, Casselman
inequality, strong-head assertion, or classification theorem. Its imports
are entirely from Mathlib.
