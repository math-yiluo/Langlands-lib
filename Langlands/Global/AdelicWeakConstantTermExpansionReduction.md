# Vanishing from square-integrable expansions of weak constant terms

`LogSquareIntegrableWeakConstantTermExistenceStatement` asserts that a logarithmically
square-integrable automorphic form `Φ` admits a weak constant term at each standard index.
This is the existence consequence of ordinary constant-term automorphy and the finite exponent
decomposition (3.2), taking the unitary exponent sum of Definition 3.7.

`LogSquareIntegrableWeakConstantTermExpansionStatement` concerns any weak constant term `ψ` of
such a `Φ` at a standard index `J`. Assume that zero is a weak constant term of `Φ` at every
strictly smaller index. Then `ψ` has `HasSquareIntegrableHeightExpansion` for the Iwasawa height
of `P_J`, so it is a finite sum of square-integrable induced forms multiplied by functions of
that height. In Delorme's setup, Proposition 3.5 uses weighted square-integrability bounds for
the archimedean derivatives to obtain temperedness. Recovering those bounds from the
weighted norm of `Φ` is part of the application to the input used here. Lemma 3.8 gives
weak transitivity and compares the smaller weak terms with those of the normalized Levi
restrictions in part (iv). After separating the exponential-polynomial factors in the
positive split-component variable, Lemma 3.10 (i) applies the square-integrability criterion
on the Levi to give the square-integrable coefficients.

Delorme fixes a maximal compact in good position with respect to the minimal Levi in §2.
The analytic premise of this reduction quantifies over every maximal compact with
minimal-parabolic Iwasawa coverage, as in `TemperedWeakConstantTermVanishingStatement`.
A proof at this scope must obtain the expansion for the given compact, or transport the
source expansion with its height, archimedean compact finiteness and square-integrability
conditions. The proof of the reduction uses the expansion and the pairing on the same
height slices for the given compact.

## Reduction proof

`temperedWeakConstantTermVanishing_of_expansion` takes the two statements as premises. Fix the
form and its orthogonality hypothesis. Induct on the number of simple roots in the standard
index. A strictly smaller index has strictly fewer roots because the set of simple roots is
finite. For a smaller index, existence supplies a weak term and induction identifies it with
zero. The expansion premise now applies to a weak term at the current index. Its orthogonality
forces it to vanish by `eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal`. At the full
index, `isWeakConstantTerm_top` identifies `Φ` itself with the weak term. The conclusion holds
at every adelic point.

Sources. P. Delorme, *On the spectral theorem of Langlands*, published PDF in the registered
`delorme-2023-spectral-theorem-langlands` collection, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, §2 on pp.5–6, (3.2) on p.10,
Proposition 3.5 on p.12, Definition 3.7 on p.13, Lemma 3.8 on p.14, and Lemma 3.10 on pp.15–16.
C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*, chapter file
`05.3_pp_40_48_Cuspidal_components.pdf` in the registered
`moeglin-waldspurger-1995-spectral-decomposition` collection, SHA-256
`ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, I.3.1–I.3.2, pp.40–43.
