# Finite averages for normalized compact Haar integration

`Langlands.RankinSelberg.equalRankNormalizedCompactIntegration` proves exactly
`EqualRankNormalizedCompactIntegrationStatement.{uF,uV,uW} F T n`. It retains
the supplied p-adic field `F`, topological data `T`, rank `n+1`, and independent
field and representation universes. It introduces no additional hypotheses.
The coefficient representations need only be smooth, and the same finite
family works for every matrix `g` and every complex spectral parameter `s`.

Install the topology, valuation and local-field instances from `T` and the
ambient general linear group's Borel structure. Write

\[
K=\mathrm{GL}_{n+1}(\mathcal O_F),\qquad
\mu=\texttt{generalLinearHaar}\ F\ n,\qquad
\kappa=\operatorname{comap}(K\hookrightarrow\mathrm{GL}_{n+1}(F),\mu).
\]

The proof identifies `K` with `Conductor.levelOpenSubgroup F.Carrier n 0`
using `Conductor.levelSubgroup_zero`. The published compactness theorem for
that open subgroup makes `K` compact; its openness makes it Borel measurable.
`comap_subtype_coe_apply` computes the total mass of `κ` as `μ(K)`, since
the image of the whole subtype is `K`. The normalization theorem
`generalLinearHaar_integralSubgroup` gives `μ(K)=1`. Thus `κ` is a finite
measure on the subtype, with total real mass one.

For `k∈K`, the proof uses the published theorem
`Conductor.valuation_det_of_mem_integralSubgroup` to obtain

\[
v(\det k)=1.
\]

This theorem follows by expressing `k` as the image of an invertible matrix
over the valuation integers and applying the determinant map to its unit.
The determinant is nonzero, because otherwise its valuation would be zero.
The discrete valuation in `T` is obtained by an ordered multiplicative
isomorphism of value groups, so it also sends `det k` to one. Consequently
`T.ord (det k)=0`, and the definition of the normalized absolute value gives
`normalizedAbsoluteValue T (det k)=1`. This implements the determinant-unit
argument directly through the published valuation theorem.

Apply `equalRankCompactIntegration` with this compact set, subtype measure,
and normalized absolute value. It supplies representatives `k_i∈K` and
nonnegative real weights `c_i`, chosen before `g,s`. Their sum is the real
total mass of `κ`, hence one. For each `g,s`, it proves integrability and the
two finite-sum identities for

\[
H_{g,s}(k)=f(gk)f'(gk)\Phi(e_{n+1}gk)|\det(gk)|_F^s
\]

on the subtype. Finally, `integrableOn_iff_comap_subtypeVal` transfers
integrability to `μ.restrict K` on the ambient group. The identities
`integral_subtype_comap` and `lintegral_subtype_comap` transfer respectively
the complex integral and the extended integral of `‖H‖ₑ`. The representatives
and weights remain unchanged, so their uniformity in `g,s` is preserved.

This is a derived specialization of the compact integration theorem using
published conductor, field-normalization and Haar-measure results, together
with Mathlib's measurable-subtype integration identities. Its source motivation
is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983),
printed p. 391, proof of Theorem 2.7, the paragraph preceding display (3)
and display (3). That passage combines compact finiteness with Iwasawa
integration. This proof handles the normalized compact averaging component;
it establishes no quotient Iwasawa identity or noncompact convergence,
rational continuation, common denominator, or normalized generator.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391, proof of Theorem 2.7, paragraph preceding (3) and display (3).
