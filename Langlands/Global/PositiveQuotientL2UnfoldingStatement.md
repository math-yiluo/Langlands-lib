# L² averaging and unfolding on the positive split-centre quotient

`Langlands.Global.PositiveRealTorus.PositiveQuotientL2UnfoldingStatement`
specializes compact quotient L² averaging to the actual adelic quotient.
It is a proposition definition, not a proof.

The field `F` is an arbitrary number field. `G` is an actual affine group
scheme of finite type over `F`. The map `i : T → G` is central, where `T`
is a commutative group scheme equipped with a specified split-torus
isomorphism indexed by a finite type `I`. Restriction of rational
characters from `G` to `T` is injective and has finite-index image. These
are the existing comparison hypotheses identifying the positive
split-centre rational quotient with the norm-one rational quotient.

The right invariance of the actual Haar measure on `normOneSubgroup F G`
is retained as an explicit hypothesis. No reductivity theorem or
unimodularity proof is inferred from the supplied algebraic data.

Let `μ+ = positiveRationalQuotientHaarMeasure F G T i`, the existing
pushforward of the canonical norm-one rational quotient measure along
`normOneToPositiveQuotient`. For each actual
`f : C_c(normOneSubgroup F G, ℂ)`, the existing function

\[
 A_f^+(q)=\int_{\Gamma^1}f(\gamma\,p(q))\,d\#\gamma
\]

is continuous and compactly supported; here
`Γ¹ = rationalNormOneSubgroup F G` and `p` is the existing inverse
quotient comparison. This is precisely
`positiveNormOneQuotientAverage`, with counting measure on the actual
norm-one rational subgroup.

There are an actual `v : Lp ℂ 2 μ+`, agreeing almost everywhere with
`A_f^+`, and a continuous complex-linear form `ℓ` such that for every
`φ : Lp ℂ 2 μ+`,

\[
 \int_{G(\mathbb A_F)^1}
   |\overline{f(x)}\,\phi(j(\Gamma^1x))|\,dx<\infty,
 \qquad
 \ell(\phi)=\langle v,\phi\rangle
 =\int_{G(\mathbb A_F)^1}
   \overline{f(x)}\,\phi(j(\Gamma^1x))\,dx.
\]

The map `j` is the actual `normOneToPositiveQuotient`. The ambient measure
is the existing `Measure.haar` on the norm-one group. The conclusion uses
`Integrable` for absolute convergence. The chosen measurable L²
representative occurs in the integral; equality with the Hilbert pairing
makes the value depend only on its class. The pairing is conjugate linear
in `v` and linear in `φ`.

## Provenance

This is an internal specialization of
`Langlands.QuotientIntegration.QuotientL2UnfoldingStatement`, using the
actual closed discrete rational norm-one subgroup, its counting measure,
the existing compatible quotient Haar measure, and the existing
measure-preserving quotient homeomorphism. No quotient measure, L²
membership or unfolding identity is supplied as a conclusion-shaped
premise.

The original motivation is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §9.2, printed pp.242–246, one-based PDF
pp.254–258, especially Lemmas 9.2.4–9.2.6 and Proposition 9.2.2. The
complete October 2026 errata corrects the compact-period quotient and the
`χδ_G` factor there. The target here specializes the generic compact
periodization step; the compact-period integration, character and modular
correction from those lemmas are not yet introduced.

## Scope

An independently reviewed exact-target proof is still required. The
statement does not identify a maximal split central torus from arbitrary
connected reductive data; it retains the stated comparison data. The
average comes from a compact test function on the norm-one group, not
from orbital integration over the full positive/principal subgroup.
It asserts no finite total quotient volume, reduction theory, smoothness,
cuspidal closedness, compact-period test separation, trace class or
spectral decomposition. Those remain obligations of the global program.
