# Cuspidality of continuous representatives on the canonical quotient

`GroupSchemeCanonicalFullAEL2ContinuousCuspidalityStatement` is set over a
number field \(F\) for an affine, locally finite type, connected reductive
group \(G\). The quotient is the Library's
`Langlands.Global.RestrictionSplitCentre.CanonicalQuotient`, with the positive
split centre \(A_G\) constructed from \(\operatorname{Res}_{F/\mathbf Q}G\).
The measure is `canonicalMeasure`.

Let \(f\) be a continuous, rational-invariant function on \(G(\mathbb A_F)\)
that is left invariant under \(A_G\). Suppose the class \(v\) in \(L^2([G])\)
is almost everywhere equal to \(y\mapsto f(y.\mathrm{out})\) for the chosen
coset representatives. Then \(v\) belongs to the full almost-everywhere
cuspidal subspace exactly when the normalized period of \(f\) along the
unipotent radical of every proper rational parabolic vanishes at every
adelic point. Each period uses probability Haar measure on the radical's
rational quotient.

The quotient convention is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §2.6, (2.19)–(2.22) and Lemma 2.6.2, printed
pp. 68–69 (PDF pp. 85–86). The proof of (9.40) in Theorem 9.7.3, printed
pp. 265–266 (PDF pp. 277–278), recovers pointwise cuspidality after
smoothing using Lemma 9.2.3, printed p. 243 (PDF p. 255). Given a
continuous representative, the equivalence here follows from the exact
measure-preserving comparison with the quotient by the positive image
of a split component of \(G\), and
`groupSchemeFullAEL2ContinuousCuspidality`, which uses continuity of the
period and full support of norm-one Haar measure.

The literature identifier is `getz-hahn-2024-automorphic-representations`.
The retained PDF has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
