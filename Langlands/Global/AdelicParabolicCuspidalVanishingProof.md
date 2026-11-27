# Parabolic cuspidal vanishing

`Langlands.Global.parabolicCuspidalVanishing` proves
`Langlands.Global.ParabolicCuspidalVanishingStatement` at arbitrary universe.
The data are an affine locally finite-type connected reductive group over
a number field, a supplied standard parabolic family, a maximal compact
with Iwasawa coverage for the family, and a positive-size closed matrix
embedding. For a family member `P`, the input is a continuous moderate-growth
function on the actual parabolic quotient. If its normalized
constant term at each standard index `Q ≤ P` belongs to the specified
fibrewise cuspidal annihilator, the function is identically zero.

The proof inducts on the size of the standard index. Compatibility of the
normalized radical averages puts every proper smaller constant term in the
scope of the induction. Their vanishing gives relative cuspidality. Every
proper rational radical of the Levi can be rationally conjugated to a
smaller standard radical intersected with that Levi. The associated radical
quotient projection preserves the normalized measures. Each right-translated
Levi fibre is rationally invariant by `isLeftInvariantUnder_leviFibre` and has
vanishing proper radical periods by `leviFibreCuspidality`. The term at `P`
is the original function, and its annihilator condition gives separation
tests on those fibres. Vanishing of
each fibre at its identity recovers vanishing at every ambient point.

On a norm-one fibre, compact smooth convolution preserves cuspidality and
produces one polynomial exponent for all archimedean derivative words from
the original function growth bound. Relative rapid decay gives a
square-integrable norm-one restriction. Fubini and the assumed pairings make
that smoothing orthogonal to every classical cuspidal test of uniform growth.
The norm-one density theorem forces its restriction to vanish. The Haar
measure has full support, and a compact smooth approximate kernel detects
any nonzero value of the original continuous function.

For the density used in this argument, the positive rational quotient is
identified measure-preservingly with the norm-one rational quotient. Smooth
compact cuspidal convolution is compact on the full cuspidal Hilbert space.
Symmetric kernels invariant under compact conjugation give spectral
approximation by nonzero eigenspaces. Their continuous representatives are
smooth and of uniform derivative growth. Invariance of these
finite-dimensional spaces under the subgroup at infinity and the actual
center action gives classical finiteness. The center action uses
`adelicEnvelopingCenterConjugation` and transfer of enveloping derivatives to
the convolution kernel.

The rank induction and the smoothing and separation step follow
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.3.4, pp. 45–46. The compact spectral step uses the operator facts in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §9.3,
pp. 246–248, around (9.12)–(9.13). The tested pairings and the parabolic
formulation are those of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
(2024), §6.2, (6.7)–(6.8), p. 202, and (8.1), p. 221.
