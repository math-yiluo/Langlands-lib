# Positive root reduction from integral opposite factors

The theorem `unramifiedRootPositiveReduction` proves the full published
`UnramifiedRootPositiveReductionStatement` at arbitrary universe `u`.
Every building, model, torus, quotient and integral section remains universally
quantified. The apartment subset is nonempty and bounded as in the statement;
the implemented argument uses its nonemptiness and does not need its bound.

The construction `unramifiedRootRadicalPreimage` is the subgroup of the actual
integral root sections obtained by pulling back `Q.radicalPoints` through
neutral-model reduction and the root-model map. Its membership lemma identifies
the subgroup with the literal reduction condition. The proof uses this subgroup
to establish the positive-depth criterion for all its sections. This construction
uses the supplied torus and quotient, with no choice of replacement data.

Write `g` for the actual generic image of the supplied integral root section
and `v` for its image in the neutral integral model. Naturality gives the exact
equality between the generic image of `v` and `g`. Injectivity of the neutral
model's integral point map identifies radical reduction of `v` with membership
of `g` in the actual radical preimage. The integral root-model image and the
zero-fixer root intersection put `g` in the root fixer of the supplied subset.

The identity lies in the radical preimage and every positive filtration, so
nonemptiness settles that case. For a nonidentity root point, the relative
rank-one factorization supplies an actual ordered normalizing opposite-factor
pair. Its Weyl action also identifies the negative root as an actual root.

Suppose first that `g` lies in the radical preimage. If it has no positive depth
at any point of the subset, its nonnegative fixer depths are all zero. V5 for
the two opposite factors makes both their negative-root depths zero at every
point, so the zero-fixer characterization makes both factors integral. The
general integral opposite-factor necessity theorem excludes radical reduction,
a contradiction.

Conversely, suppose `g` has positive depth at one point. If it lay outside the
radical preimage, `HenselianIntegralOppositeFactors` would make both prescribed
opposite factors integral. Here the actual maximal-unramified valuation ring
is a Henselian DVR with algebraically closed, hence perfect, residue field.
The supplied split integral torus is used unchanged via `toIntegralTorusData`.
The first opposite factor would therefore have nonnegative negative-root depth
at the same point. V5 says that this depth plus the positive original depth
is zero, which is impossible.

This is an internal composition of the imported root-factor, valuation and
integral-model theorems. It proves the existential point criterion in the
published statement; it does not replace it with positivity at every point.
