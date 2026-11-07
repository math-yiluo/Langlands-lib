# Rank-one pair factors from a supplied normalized reciprocity family

This internal corollary combines `BaseGeometricResidue` with
`RankOnePairFactorCompatibility`. The prime and p-adic field are arbitrary.
The field, Weil-parameter carrier, two automorphic carriers and supplied
local-constant-system carrier have independent universes.

`NormalizedRankOnePairFactorCompatibilityStatement` quantifies over every
supplied common-closure reciprocity family satisfying `NormalizedReciprocity`
and every supplied local-constant assignment certified as a system for that
family. The explicitly constructed `baseReciprocityCandidate` then satisfies
the existing `RankOnePairFactorCompatibilityStatement`. Thus, for every
nontrivial additive character and pair of actual irreducible rank-one Weil
classes, a self-dual additive Haar measure exists. At every such supplied
measure, the two actual rank-one reciprocity images have a certified JPSS
L-polynomial whose reciprocal is the arithmetic pair L-factor, and a single
coefficient/exponent pair satisfies both full epsilon-factor relations.

The first theorem applies the proved geometric normalization of any
compatible base candidate to the existing separate pair-factor theorem.
The proof of the named proposition specializes this to the explicit base
candidate, whose base compatibility is already proved. Neither a standalone
candidate nor its geometric normalization is an extra premise of this
proposition.

The final theorem applies the same full conclusion to the rank-one values
of any two supplied supercuspidal maps satisfying the original
`SupercuspidalRankOneCompatibility` along a compatible base candidate.
Its proof rewrites these values using the established equational
characterization of rank-one compatibility and applies the first theorem.
It retains both self-dual-measure quantifiers and the separate full L-
and epsilon-factor certificates.

This provenance is entirely internal: the geometric theorem proves the
finite norm-residue and residue-action conditions, and the pair-factor
theorem supplies the analytic/arithmetic comparison. This unit constructs
no normalized reciprocity family, local-constant system or all-rank
supercuspidal map. Their stated premises remain explicit. Higher-rank
compatibility and the unchanged closed supercuspidal correspondence
remain separate obligations.
