# Positive-quotient trace comparison (proof)

`Langlands.TraceFormula.positiveQuotientTraceComparison.{u}` proves the published
`Langlands.TraceFormula.PositiveQuotientTraceComparisonStatement.{u}` without changing
its hypotheses, operators or measures. Write `A⁺` for `intrinsicSubgroup F T`, `N` for
`normOneSubgroup F G`, and `Q⁺` and `Q¹` for the positive and norm-one rational quotients.
All Hilbert spaces below use the Library's quotient Haar measures.

## Implemented proof

1. **Continuity and support of the mean.** Pull `f` back as a compactly supported
   continuous map along the homeomorphism `d = normOneDecomposition`, using
   `f.comp d.toCocompactMap`. Use `QuotientIntegration.compactIntegralFullFactor`
   (`Langlands.Analysis.Local.QuotientProductFactor`) to integrate out `A⁺` for
   `normalizedPositiveHaarMeasure`. That construction uses the compact first
   projection of the pulled-back support for continuity of the parameter integral,
   and the compact second projection to contain the support of the result. Its
   underlying function is exactly the statement's `fOne`, since `d(a,n) = a n`
   with `a` mapped by `positivePointMap`.
2. **Pullback and right actions.** The measure-preserving equivalence
   `j = positiveQuotientMeasurableEquiv : Q¹ ≃ᵐ Q⁺` induces the linear isometry
   `U : L²(Q⁺) → L²(Q¹)` by `Lp.compMeasurePreservingₗᵢ`; pullback along `j.symm`
   is its inverse by the composition and identity laws for `Lp` pullback. The
   hypothesis identifying `π` with right translation yields equality in `Lp`
   with the pullback by the norm-one quotient translation. The two Library
   notations for that translation agree on coset representatives. For an ambient
   element `g`, `positiveQuotientHomeomorph_rightTranslate` intertwines translation
   by `g` on `Q⁺` and translation by `p(g)` on `Q¹`, where `p = normOneProjection`.
   Composing the measure-preserving pullbacks therefore gives
   `U (ρ(g) v) = π(p(g)) (U v)` for every `v`. In particular, on product coordinates
   `p(d(a,n)) = n` by multiplicativity, since `p` kills the positive factor and
   restricts to the identity on `N`.
3. **Intertwining the integrated operators.** For fixed `v`, the orbit weighted
   by `f` is Bochner integrable by `haarQuotientL2ActionIntegrand_integrable`.
   Commute `U` with its integral as a bounded linear map, and use
   `measurePreserving_normOneDecomposition` to change to the normalized product
   measure with no scalar factor. The transformed vector-valued integrand is
   integrable by measure preservation. `integral_prod_symm` then integrates over
   `A⁺` first. The pointwise intertwining from step 2 leaves the vector
   `π(n) (U v)` constant in the inner integral, so `integral_smul_const` gives
   `fOne(n) • π(n) (U v)`. This proves `U (R(f) v) = π(fOne) (U v)` using the
   applications of the two integrated actions, not an integral in operator norm.
4. **Trace comparison.** The private trace helper rewrites `π(fOne)` as
   `U R(f) U⁻¹` and `R(f)` as `U⁻¹ π(fOne) U`. It uses the published bounded
   rectangular cyclicity theorem `operatorTraceCyclicity`
   (`Langlands.Analysis.OperatorTraceProof`) in each direction for trace-class
   membership. If `R(f)` is trace class, cyclicity and `U⁻¹ U = 1` give the trace
   equality. Nothing about trace equality outside trace class is used or proved.

## Source correspondence and scope

This is a derived comparison, not the simple trace formula. In J. R. Getz and
H. Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, §2.6, (2.19)–(2.22) and Lemma 2.6.2
(printed pp. 68–69; PDF pp. 85–86) give the norm-one and central quotients and
explain their right-action comparison in the reductive number-field setting.
Corollary 18.4.1 (printed p. 485; PDF p. 492) uses test functions already on the
central quotient and fixes quotient Haar measure to define its operators. The
Lean proof implements the intervening passage from an ambient test function to
its positive-factor average using the Library's explicit split-torus data and
exactly normalized measures. It quantifies over the supplied `π`; it does not
construct `π`, prove either operator is trace class unconditionally, or evaluate
any trace or orbital integral.
