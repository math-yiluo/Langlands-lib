# Differentiation of the L² classes of cusp forms on GLₙ

Author: Worker 1033. The proposition is
`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalFormClassDerivativeStatement`.
This module defines the proposition; it does not prove it.

## Statement

Use the data of `GeneralLinearCuspidalSummandRealizationStatement`: a number
field `F : Type u` with compact adele quotient, rank `n = r + 1`, parabolic
dynamic data `hPD`, the central split-torus datum `(T, i, hi, I, e, hc)` with
injective finite-index character restriction, and the right-invariance
hypothesis on norm-one Haar measure. Write `S` for the full almost-everywhere
cuspidal subspace of `L²` on the positive-central rational quotient in these
data. Its right translation action is `πc`.

Let `R` be a cuspidal operator realization in rank `n`, `f : R.Space`, and
`X : ArchimedeanGL.RealLieAlgebra F n`. Write `a(t)` for the group-scheme adelic
point obtained from `realLieExponentialCurve F n X t` by `AdelicGL.ofInfinite`
and the inverse of `GeneralLinearGroupPoints.adelicHomeomorph`. If `φ, ψ : S`
are the `L²` classes of the functions of `f` and `R.realization.lieAction X f`,
respectively, then `t ↦ πc(a(t)) φ` has derivative `ψ` at `0`, in the norm of
`S` and over the real time parameter.

Both identifications are the published `IsGeneralLinearFormClass` predicate:
there is a continuous function on the positive-central rational quotient
whose pullback is the continuous function of the form and which represents
the given class almost everywhere. The proposition assumes these two
identifications; it does not assert that the classes exist for every form,
that every cuspidal vector comes from a form, or that this orbit is smooth
in all adelic variables.

## Provenance

This is a derived comparison lemma in the Library's vocabulary, not a
verbatim theorem of Getz–Hahn. Their *An Introduction to Automorphic
Representations* (2024), Theorem 6.6.4 and proof (p. 172; PDF p. 186), compare
a discrete automorphic Hilbert representation with its automorphic
representation of finite vectors. Theorem 9.7.3 and the proof of (9.40)
(pp. 265–266; PDF pp. 277–278) compare the two cuspidal models. The opening
of that proof uses the boundedness supplied by Theorem 9.7.1 (p. 264;
PDF p. 276) to put cusp forms into `L²`. The present proposition starts
with the two `L²` classes already given and isolates the identification of
the two infinitesimal actions on such vectors. It does not assert the
rapid-decay theorem or the full comparison of the sources.

Original source: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The October 2026 author errata, p. 2, §6.6, correct the display on p. 171
and a reference in the proof of Theorem 6.6.2, not Theorem 6.6.4; the
Chapter 9 entries on errata pp. 2–3 do not concern §9.7. Errata source:
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
