# Regular integral symmetrization in semisimple rank at most one

Author: Worker 1547.

This internal construction combines the published regular refinement, rank-one
integral symmetrization, and generic-centralizer theorem. All fields have
arbitrary universe `u` and arbitrary characteristic.

For a split torus homomorphism `i : T → G` into an affine group locally of finite
type and an actual normalizing rational point `n`, the definition
`regularNormalizerSymmetrizedCocharacter hT i n ν` first takes the published
`regularRefinement hT i ν`, denoted `μ`, and then forms `η = μ - w μ` in the
actual integral cocharacter lattice, where
`w = cocharacterAut (normalizingAut i n)`. It remains a cocharacter of the
same torus. The definition itself requires neither reductivity nor maximality.

The theorems assume that `G` is connected reductive, `i` is a maximal torus,
and every pair of actual roots is integrally dependent. For a supplied
nonidentity class of `n` in the actual relative Weyl quotient, the published
pairing-doubling theorem gives
`⟨α, η⟩ = 2 * ⟨α, μ⟩` for every actual root `α`.
The refinement is regular, so these integer pairings are nonzero. This proves
`isGeneric_regularNormalizerSymmetrizedCocharacter`. The published positive-sign
preservation of regular refinement, followed by multiplication by the positive
integer two, proves `regularNormalizerSymmetrizedCocharacter_pos`: every root
positive on the original `ν` is positive on `η`. No division by two or
reduction of the pairing to the base field occurs.

The exact identity `w η = -η` uses the published involution on the entire
integral lattice and holds for any supplied normalizer point; these two negation
theorems do not require its class to be nonidentity. The corresponding
group-homomorphism theorem states that conjugating `η → T → G` by `n` gives
the homomorphism of `-η`. It applies to the whole cocharacter, including any
central directions, and does not infer the identity from root pairings alone.

Finally, `centralizer_regularNormalizerSymmetrizedCocharacter` uses
`genericCentralizer`. Split maximality converts the given
maximal torus into a maximal split torus, and the genericity just proved
identifies `Dynamic.centralizer (η → T → G)` with `torusCentralizer i`.
This is equality of the actual subgroup functors on every relative test
scheme, including nonreduced tests.

The provenance is internal composition of
`Absolute.RegularRefinement`,
`Rational.RankOneCocharacterSymmetrization`,
`Rational.GenericCentralizerProof`, and
`Torus.MaximalSplitComparison`. This module does not construct a nonidentity
normalizer class, show that the torus centralizer is contained in a prescribed
subgroup, construct a homogeneous quotient, or prove positive-root uniqueness.
Those application inputs remain separate obligations.

The generic-centralizer input uses the existing open-cell and connectedness
proofs. `Absolute.OppositeCellStatement` now contains the unchanged open-cell
proposition separately from `Absolute.BorelStatement`, so the existing proof
chain avoids the classification statement module. The duplicate rank-one
open-cell, connectedness and generic-centralizer copies are consolidated into
that shared chain.
