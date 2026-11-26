# Square-integrable height expansions under infinite compact conjugation

`AdelicSquareIntegrableHeightConjugateCompactStatement` transports a finite square-integrable
height expansion at a standard parabolic by right translation. If `a` is an infinite adelic
point, the expansion of `g ↦ ψ(g a)` uses the conjugate Iwasawa compact `a K a⁻¹`. The theorem
`adelicSquareIntegrableHeightConjugateCompact` gives Iwasawa coverage for that compact and proves
the transport. Each coefficient form is right translated, and the height difference shifts the
argument of its scalar coefficient.

The underlying membership result `StandardParabolicFamily.isSquareIntegrableInducedForm_infiniteRightTranslate`
uses the inducing space of Lapid, *On Arthur’s Asymptotic Inner Product Formula of Truncated
Eisenstein Series*, §2, printed p. 311 (volume PDF p. 320, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`). The compact integration uses
the Haar probability in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.1.13, printed p. 18 (`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, file SHA-256
`f629f59c8774b80b155f60ef935ceccd4c5c1e87a1ea793baec0875749e770`, registered under
`moeglin-waldspurger-1995-spectral-decomposition`). The height expansion is the form of the
conclusion of Delorme, *On the spectral theorem of Langlands*, Lemma 3.10 (i), PDF pp. 15–16
(`Delorme--On the spectral theorem of Langlands--2023.pdf`, file SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, registered under
`delorme-2023-spectral-theorem-langlands`).

Write `a = p k₀` by Iwasawa decomposition for the first compact and factor `p = m₀ u` into Levi
and radical parts. In the integral for the conjugate compact, parametrize `k'` as `a k a⁻¹`.
The translated function at `m k'` becomes its original value at `m m₀ k₀ k` by left radical
invariance. The weighted square changes by the fixed modulus of `m₀`. The substitutions on the
compact and on the canonical Levi quotient preserve the respective measures. Right translation
commutes with the left split-component action and carries the automorphy predicate to the
conjugate infinite compact. Iwasawa decomposition gives `H_K(g a) = H_{a K a⁻¹}(g) + H_K(a)`.
Applying this identity to the original scalar coefficients proves the expansion formula.
