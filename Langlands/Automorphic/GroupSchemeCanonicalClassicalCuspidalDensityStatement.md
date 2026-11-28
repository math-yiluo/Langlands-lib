# Classical cuspidal density on the canonical adelic quotient

`Langlands.Global.RestrictionSplitCentre.GroupSchemeCanonicalClassicalCuspidalDensityStatement`
identifies the norm closure of `canonicalCuspidalFormL2Image` in \(L^2([G])\)
with `canonicalFullAEL2CuspidalSubmodule`. Here \(F\) is a number field in
universe zero and \(G\) is an affine locally finite-type connected reductive
group over \(F\). The proposition fixes a maximal compact subgroup at
infinity, a closed matrix realization of positive size and a smooth relative
dimension. The parabolic-dynamic witness specifies the proper rational
parabolic radicals. The actual archimedean differential commutator is
`adelicDifferentialCommutator_of_smooth`.

Both subspaces use the same Haar measure on
\([G]=A_G G(F)\backslash G(\mathbb A_F)\), transported from the norm-one
rational quotient by the canonical split-centre comparison. The classical
image consists of classes of square-integrable continuous functions on
\([G]\). Their adelic pullbacks have smooth archimedean slices, a common
open finite level, compact and infinitesimal finiteness, and moderate
height growth. The normalized periods over the compact rational quotients
of all proper parabolic radicals vanish at every adelic point. The full
cuspidal subspace uses convergence and vanishing almost everywhere for the
periods evaluated on norm-one adelic points. The measures on the radical
quotients have mass one in both conditions.

The target is the density assertion at the start of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 9.7.3,
printed pp. 265–266 (PDF pp. 277–278), formulated for the Library's
classical carrier. Its slice-wise smoothness and common finite level follow
the convention in Borel–Jacquet, *Automorphic Forms and Automorphic
Representations* (1979), §§4.1–4.3, printed pp. 194–195 (PDF pp. 189–190).
Getz–Hahn's algebraic tensor convention in (6.1), printed p. 158
(PDF p. 172), also requires the archimedean slices to span a
finite-dimensional space. The Library's carrier imposes global moderate
height growth and incorporates square integrability in the image.

The argument uses the canonical measure-preserving comparison with the
positive-torus quotient and the positive-quotient theorem
`groupSchemeClassicalCuspidalHilbertDensity`. Its compact-operator
approximation uses the symmetric mass-one kernels and compact spectral
theorem of Getz–Hahn §9.3, printed pp. 246–247 (PDF pp. 258–259).
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
§I.3.4, printed pp. 45–46 (chapter PDF pp. 6–7), uses a related density step
in the \(L^1\) pairing in the proof of the cuspidal-component vanishing
criterion. The closure here uses the \(L^2\) norm of the canonical measure.

Registered sources

- `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
- `borel-jacquet-1979-automorphic`,
  SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
- `moeglin-waldspurger-1995-cuspidal-components`,
  SHA-256 `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`.
