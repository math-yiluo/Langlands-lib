# Complementary prefixes and the strict positive root cone

`Langlands.Exponents.ComplementaryPrefixConeObstructionStatement` is an
internal finite-sum proposition. Let `x : Fin r → ℝ` be any vector and let
`S` be a finite subset with both `S` and its entire complement nonempty.
Suppose permutations `e` and `f` place exactly `S` and exactly `Sᶜ` in their
first `S.card` and `Sᶜ.card` positions, respectively. Then the two permuted
vectors `x ∘ e` and `x ∘ f` cannot both lie in `IsPositiveRootCone`.

Here a permutation sends each new position to its original index. Thus the
membership hypotheses mean that the indicated prefixes contain every index
of the specified subset exactly once, with no discarded or repeated index.
The cone predicate requires total sum zero and strictly positive sums for
every nonempty proper prefix. These two particular prefixes would make the
sums over `S` and `Sᶜ` both positive, although they add to the total zero.

The provenance is elementary reindexing of finite sums and additivity over
a finite subset and its complement. No representation-theoretic input is
asserted or assumed. In the intended application, each `x i` already
contains its individual block-rank weight. The proposition imposes no
equal-rank condition and no equality among distinct coordinates; repeated
representation factors remain separate indexed terms.

This file defines the proposition and supplies no proof of it. It neither
constructs permutations nor transfers actual Jacquet occurrences, and it
does not establish integral cuspidal Jacquet-word existence.
