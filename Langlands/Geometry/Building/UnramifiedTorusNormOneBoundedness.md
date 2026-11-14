# Norm-one tori over the actual maximal unramified field

Worker 336. This internal specialization for Task 6432 derives the torus
boundedness step from the spectral torus helper. Its source motivation is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 2.5.8,
printed pages 88–89 / PDF pages 119–120. The precise statement for the Library's
constructed maximal unramified field and its normalized valuation is derived
content. The November 2024 corrections to the valuation homomorphism's sign
leave this common kernel unchanged.

`TorusNormOneBoundedStatement` says that for every nonarchimedean local field
\(F\) and actual affine torus \(T\) over \(K=\texttt{inertiaFixedField F}\), the
subgroup `characterValuationKernel (valuation F) T` is algebraically bounded.
It uses exactly `ValuativeRel.ofValuation (fixedFieldValued F).v` on \(K\).
The assertion is universe-polymorphic in the common universe of the fields.
The theorem `torusNormOneBounded` proves this statement.

The proof first identifies the carrier of the character kernel with
`spectralCharacterUnitLocus F K T`. For each rational character, the published
equivalence between the normalized integer valuation and `fixedFieldValuation`
identifies their valuation-one conditions. The published equality of the
fixed-field and spectral valuations then gives the asserted equality of sets.
The same valuation equality identifies the prescribed valuative relation with
the spectral relation. The generic spectral torus theorem therefore applies.
The complete nontrivially normed ultrametric structure used in that theorem
is supplied by the original local field \(F\); no completeness or local-field
instance is imposed on \(K\).

`isAlgebraicallyBounded_image_characterValuationKernel` transports this bound
along any homomorphism of affine group schemes, using the existing pullback
theorem for regular functions. `centralizerNormOneBounded_of_isTorus` applies it
to the actual centralizer inclusion in supplied building data. Affineness of
the supplied centralizer follows from its closed immersion into the affine
ambient group. This last result explicitly assumes that the actual centralizer
is a torus. This module does not prove that structural assertion and does not
prove `CentralizerNormOneBoundedStatement` without an additional input.
