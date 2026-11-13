# Reduction of the rank-one outer-A Hermitian model

This internal reduction proves
`outerTypeARankOneHermitian_of_presentation_and_splitRank`. Its two explicit
premises are the complete propositions
`OuterTypeAHermitianPresentationStatement` and
`HermitianMatrixSplitRankStatement`, at the same arbitrary universe `u`.
Its conclusion is exactly `OuterTypeARankOneHermitianStatement` at that
universe. It retains arbitrary fields and every characteristic.

The proof unpacks the actual rank-one outer-A index. Its rank is two or
three, and its numbering supplies all type-A Cartan entries, the full
two-element star image, and the distinguished endpoints. The supplied
presentation theorem then produces a separable quadratic extension, a
nonsingular Hermitian matrix, and a faithful, exact, natural matrix
presentation on every test scheme. The additional embedding, torus
characters, and root-restriction conclusions of that theorem are not
needed for this reduction.

The determinant witness makes the matrix an actual general-linear
element. It is packaged as `HermitianMatrix.Form`; the existing
`linearFirst` pairing has the full formula
`bar(b)` dotted with `J.mulVec a`. The general matrix interface supplies
Hermitian symmetry and nondegeneracy of this pairing.

The supplied split-rank theorem gives an actual totally isotropic
submodule attaining `splitRank G` and a dimension bound on every such
submodule. Rewriting the given equality `splitRank G = 1` and the full
pairing formula yields precisely the attained dimension-one and
maximality hypotheses for
`HermitianRoot.SchemeModel.rankOneModelOfAttainedPresentation`.
That construction returns a diagonal middle on `Fin (n - 1)`, units with
the required exact weight equations, anisotropy, and an actual
group-scheme isomorphism to the existing Hermitian equalizer model.
The proof returns these same data in the target existential.

`OuterTypeARankOneHermitianModel` packages the extension field, its field
and algebra structures, the quadratic and separability proofs, and the
actual `RankOneModel` over that extension in a dependent tuple.
`outerTypeARankOneHermitianModelOfPresentationAndSplitRank` uses classical
choice on the proved conditional existential to select this tuple,
including the isomorphism itself. It has the same two explicit proposition
premises and all the host statement's group and index hypotheses.

The provenance is internal composition of the named matrix-pairing,
split-rank, and coordinate-model interfaces. This module does not prove
either of its two proposition premises. An unconditional proof of the
host statement still requires actual proofs of those premises. No
local-field classification or Kneser–Tits consumer enters this reduction.
