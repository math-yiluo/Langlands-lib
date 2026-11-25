# The exact inner-type-A index at split rank one

A simply connected, absolutely almost-simple group of inner type A and split
rank one over any field has the actual index `¹A_(2d−1),1^(d)`. Here `d` is the
positive reduced degree of the division algebra in an actual binary reduced
norm-one model of the group. Every Cartan entry, the exact singleton of
distinguished vertices, and triviality of the full absolute Galois star action
are retained. There is no characteristic or local-field restriction.

The first theorem gives a more general marked-position calculation: for a
simply connected actual index with split rank one, a full type-A Cartan
numbering and trivial full star action, the distinguished vertices are precisely
those at zero-based position `j` with `2j+1=n`. The published rank-one orbit
theorem makes the distinguished set a singleton. Actual opposition preserves
this singleton and, by `TypeAOpposition`, reverses the chain. Thus the singleton
is fixed by reversal, giving the equation. Injectivity of the numbering proves
the reverse implication as well.

`IndexedBinaryNormOnePresentation` retains the degree-preserving binary
presentation and additionally certifies `HasRankOneInnerAIndex` at that same
algebra's reduced degree. Its unconditional nonemptiness proof uses the
published `innerTypeARankOnePresentation`, whose degree equation is `2d=n+1`.
Together with the marked-position calculation, this gives exactly one-based
marked position `d` on the `2d−1` vertex diagram. The construction chooses this
presentation; the last theorem extracts the exact inner-A alternative.

This module is an internal composition of the imported structural and elementary
root-datum results. The binary model comes from the actual inner-type-A
norm-one identification, matrix division-algebra decomposition and matrix
norm-one split-rank formula, as explained in `InnerTypeARankOneProof.md`.
Opposition is derived from actual compatible Tits data, and its type-A
identification uses the Weyl-invariant weight residue, as explained in the
imported pairs. No local rank-one classification or Kneser–Tits result is used.
The other Cartan types and outer star actions, and hence the unconditional
full local enumeration, are outside this module; `localRankOneTitsIndex` in
`LocalRankOneTitsIndexProof` proves that enumeration,
`LocalRankOneTitsIndexStatement`.
