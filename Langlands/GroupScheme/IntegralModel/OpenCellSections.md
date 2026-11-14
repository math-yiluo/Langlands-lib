# Integral open-cell sections detected on the special fibre

This module proves the local-spectrum factorization in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 8.1.1, printed pp. 283–284
(PDF pp. 314–315), and a derived formulation for actual integral group models.
The registered original is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered corrections `kaletha-prasad-2024-corrections`, version of
1 November 2024, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 37–38, do not change Lemma 8.1.1.

All declarations are at arbitrary universe `u`. For a commutative local ring
`R`, an open immersion `j : X → Y`, and a morphism `x : Spec R → Y`,
`range_subset` proves that the image of `x` lies in the image of `j` whenever
the image of the closed point does. Every point of the spectrum specializes
to its closed point, and membership in an open subset passes to
generizations. `localOpenLift` applies the actual open-immersion lifting
construction to this containment; `localOpenLift_fac` proves that its
composition with `j` is `x`. `exists_lift_iff` states the resulting
factorization criterion in both directions.

For schemes `P` and `Q` over `Spec R` and a supplied open immersion
`c : P → Q` over that base, `openSectionEquiv` identifies sections of `P`
with sections of `Q` whose closed point lies in the image of `c`. Its
forward map is postcomposition by `c`, as `openSectionEquiv_val` records.
The inverse is `localOpenLift`; compatibility with the base follows from
the section equation and the fact that `c` is a morphism over `Spec R`.
The inverse identities follow from its factorization equation and the
monomorphism property of an open immersion.

The final theorem `section_lifts_iff_reduction_lifts` concerns a supplied
integral model `M` of a group over the fraction field `K` of a local domain
`R`. Let `j : P → M.group.X` be a supplied open immersion over `Spec R`.
An original integral section `x` factors through `j` if and only if its
actual reduction `M.reduction x` factors through the base change of `j`
to `Spec (R/𝔪)`. A factorization over `R` gives the residue factorization
by an explicit pullback lift. In the reverse direction, composing the
residue factorization with the pullback projections shows that the closed
point of `x` lies in the image of `j`; `openSectionEquiv` then gives its
integral factorization.

This residue formulation and the section equivalence are internal derived
infrastructure for the open-cell step of KP Theorem 8.2.9 (printed
pp. 293–295 / PDF pp. 324–326). They use the published actual integral-model
and reduction definitions. There is no Henselian, smoothness, completeness,
or algebraic-closure hypothesis. The module assumes a supplied open chart;
it does not construct a root-group cell or prove the opposite-factor theorem.
