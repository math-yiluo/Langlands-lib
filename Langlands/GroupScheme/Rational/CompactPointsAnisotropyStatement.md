# Compact rational points force anisotropy: affine target

Author: Worker 1563.

`Langlands.GroupScheme.CompactPointsAnisotropyStatement.{u}` is the
compactness-to-anisotropy auxiliary target for the whole-group compactness
theorem. For every actual nonarchimedean local field `F : Type u` and every
actual affine group scheme `G` over `Spec F`, compactness of all actual
rational points in the explicitly installed canonical
`rationalPointTopology F G.X` implies `IsAnisotropic G`. The latter is the
published condition `splitRank G = 0`.

This is a derived strengthening of one implication of the published
`Langlands.GroupScheme.AnisotropicCompactnessStatement`: the compactness
obstruction needs affineness but does not need connectedness or
reductivity. In the main target, affineness is obtained from its existing
connected reductivity witness. The target includes every field
characteristic, every finite split-torus rank, and arbitrary universe `u`.
It asserts no converse.

The source motivation is Kaletha--Prasad, *Bruhat--Tits Theory: A New
Approach* (2023), Theorem 2.2.9, printed pp.71--73 / PDF pp.102--104, with
the compactness consequence on printed p.72 / PDF p.103. Registered source
`kaletha-prasad-2023-bruhat-tits-new-approach` has SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 1 November 2024 corrections, PDF pp.24--25, supply the standing
Henselian and separability-or-discreteness qualifications for the source
section. Registered source `kaletha-prasad-2024-corrections` has SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The actual local-field hypotheses remain unchanged.

The planned direct proof uses the published closed-embedding comparison
on canonical rational points and the split-torus point homeomorphism.
A nontrivial split torus has a continuous surjection to the field unit
group, whose valuations are unbounded. This explains the stronger affine
scope; this file records the proposition only.
