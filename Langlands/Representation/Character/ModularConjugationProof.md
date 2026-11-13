# Conjugation of admissible characters with the modular factor

Worker 278. This proof unit targets the unchanged
`Langlands.CharacterConjugationModularStatement`, with the independent universes
of the group and the representation space and no additional hypotheses.
The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, III.1.12 Lemma,
printed p.65 / PDF p.71.

The internal construction `Character.scalarActionTest` bundles the function
`x ↦ f(x) L(ρ(x)v)` as a Schwartz–Bruhat test function. Smoothness makes the
orbit coefficient locally constant, and its product with `f` has compact support.
No topology or continuity assumption is imposed on the representation space or
on its algebraic linear functional `L`.

For the integrated operator, apply the published scalar Haar translation
formula `Distribution.RenardModular.translation` to the coefficient test
`y ↦ f(y) L(ρ(a⁻¹)ρ(y)ρ(a)v)`, with both translation parameters equal to `a`.
Its integrand after translation is `f(axa⁻¹)L(ρ(x)v)`. The integrated-action
pairing formula and algebraic-dual separation give
`ρ(f ∘ Int(a)) = δ_G(a) ρ(a⁻¹)ρ(f)ρ(a)`.
The scalar translation theorem applies to the supplied left Haar measure
without any countability or inner-regularity assumption.

The resulting finite-rank operator is a scalar multiple of a conjugate of the
original operator. Linearity and conjugation invariance of
`FiniteRankEnd.trace` prove `Character.distribution_conjugation_modular`.
Finally `characterConjugationModular` supplies the actual pullback test function
and proves the exact published proposition.

The coefficient construction and reduction from scalar integrals are internal
derived arguments. The scalar measure transformation and finite-rank trace
theorems used here are already published Library results.
