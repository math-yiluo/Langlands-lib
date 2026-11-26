# Integrating against the limit of a translated or damped cone

`tendsto_integral_remove_exponential_damping` takes an integrable test and a
damping exponent that has a measurable version and is almost everywhere
nonnegative for the same measure. Along positive parameters approaching zero,
the damped test converges pointwise to the original test. Its norm is bounded
almost everywhere by the norm of the original test, so dominated convergence
gives convergence of the integral. The measure can be the restriction of a
measure to an oriented cone.

`TranslatedConeIntegralLimitStatement`, proved by `translatedConeIntegralLimit`,
describes the integral limit for an integrable test as \(n\) tends to infinity
through the natural numbers. Each \(\ell_i\) is measurable, so the integration
regions are measurable. For fixed \(x\), the translated coordinates
\(\ell_i(x)+n v_i\) grow to \(+\infty\) because all \(v_i>0\). There are finitely
many coordinates, so they are eventually simultaneously positive. The indicator of the conditions
\((\ell_i(x)+n v_i)\varepsilon_i>0\) therefore tends to one if all
\(\varepsilon_i>0\), and to zero otherwise. The proof bounds the norm of each
restricted test by the original test's norm and applies dominated convergence.
An empty set of defining coordinates gives the full integral.

The damping argument is the dominated-convergence step of P. Delorme,
*Troncature pour les espaces symétriques réductifs*, Acta Math. 179 (1997),
§9, (9.1) and Lemma 11, printed p. 72 (PDF p. 32).
The registered source `delorme-1997-reductive-symmetric-space-truncation`
has SHA-256 `02eb996aa75322ecb3294cbe839dd9cc2b37077d781455e49128a2f01e0dc70c`.
The translated integral argument applies after expressing the fixed direction
and the oriented cone in their defining coordinates, as in Delorme,
*On the spectral theorem of Langlands*, §7, Proposition 7.8 and the proof of
Lemma 7.11, PDF pp. 33 and 35. The published PDF of
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
