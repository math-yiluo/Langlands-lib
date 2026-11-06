# Convergence of the actual rational source gamma integral

This derived adapter concerns Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)*, I.1, printed p.240 / PDF p.6:
the common-compact mass-one Haar convention, the second formula (2), and
the gamma integral immediately preceding Remark (3). Source:
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source uses a special compact subgroup and semistandard parabolics.
The Lean adapter displays the precise properties used, without claiming
their existence for an arbitrary chosen compact open subgroup.

The field is an arbitrary-universe nonarchimedean local field, in any
characteristic. The group scheme is affine and locally of finite type.
Rational points have their canonical rational-point topology and its Borel
measurable structure. Separation, local compactness, second countability and
the nonarchimedean group property come from the existing rational-point
results. The actual dynamic parabolic, its canonical Levi and radical, and
the opposite radical of the inverse cocharacter are the original subgroups.
All subgroup Haar measures are the already constructed intrinsic measures
with mass one on intersection with the same supplied compact open `K`.

`gammaReal` is exactly `gamma.toReal`, with no rescaling or new parameter.
Its definition does not require smoothness, Iwasawa factorization, limit
stability, or a chosen ambient measure.

For `gamma_ne_zero_ne_top`, `gammaReal_pos`, and `ofReal_gammaReal`, the group
scheme is additionally smooth and a left and right invariant ambient Haar
measure is supplied explicitly. Closedness gives local compactness of the
literal dynamic subgroups. The published
`isOpenEmbedding_openCellMap_rationalPoint` supplies the actual open cell.
The local lemma in `LocalOpenCellGamma` then proves that the original gamma
is finite and nonzero. Real positivity and recovery by `ENNReal.ofReal`
follow from the standard finite-value conversion lemmas. No reductivity,
splitness or quasisplitness restriction is needed for this conditional result.

The scalar integral comparisons additionally assume `G(F)=P(F)K`, stability
of `P(F) ∩ K` under the actual dynamic limit map, and right invariance of the
actual normalized Levi Haar. These hypotheses are the same displayed
premises as the existing exact lower-integral comparison
`gamma_eq_lintegral_of_levi_rightInvariant`. Actual radical right and inversion
invariance are already proved in `RationalDynamicSourceHaar`.

`integrable_iwasawaModulus` uses the existing local constancy of the real
Iwasawa modulus. Restriction to the opposite radical is continuous and thus
strongly measurable. The scalar is everywhere positive. Its lower integral
equals the original gamma by the existing comparison, so the proved
finiteness gives a finite integral of its norm. This establishes genuine
Bochner integrability; continuity or measurability of selected Iwasawa
components is not assumed.

`gammaReal_eq_integral` converts that nonnegative lower integral to the
Bochner integral and identifies it with the original gamma's real value.
These are convergence and exact-scale results for actual rational subgroups
under the stated premises. They do not use or establish conullness of the
whole cell. A global integration formula still needs the independently
owned conullness proof. Special-compact existence, general ambient and Levi
unimodularity, arbitrary same-Levi independence and the main Plancherel
conclusions remain separate obligations.
