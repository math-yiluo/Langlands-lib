# Extension from maximal-unramified integral points

The theorem
`Langlands.GroupScheme.IntegralModel.unramifiedSmoothHomExtension` proves
exactly the published proposition
`UnramifiedSmoothHomExtensionStatement.{u}`. For a nonarchimedean local
field `F : Type u`, a smooth integral group-scheme model `M` over `𝒪[F]`,
an arbitrary model `N`, and a generic homomorphism `f : G ⟶ H`, preservation
of the integral-point images after maximal unramified base change implies
`Nonempty (M.Hom N f)`. The resulting morphism is over the original
integers `𝒪[F]` and has the specified generic map `f`.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Corollary 2.10.10 and the second part of Remark 2.10.19, printed pp. 124
and 127 / PDF pp. 155 and 158. The conventions for the maximal unramified
extension and its integers are on printed p. 121 / PDF p. 152. The
registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered authors' corrections `kaletha-prasad-2024-corrections`
(1 November 2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
do not amend Section 2.10: the Chapter 2 entries pass from Section 2.6 to
Section 2.11.

## Applying the strictly Henselian theorem

The proof takes the coefficient ring to be `fixedFieldIntegers F` and its
fraction field to be `inertiaFixedField F`. It installs the canonical
valuation-integer algebra from `𝒪[F]` to this ring and the associated
scalar tower. These are exactly the instances used in the definition of
`IntegralModel.baseChangeUnramified`.

The published arithmetic supplies all the hypotheses of the strictly
Henselian extension theorem:

- `fixedFieldValuesFromBase F` and
  `fixedFieldIntegersIsDVR_of_valuesFromBase` give the discrete valuation
  ring structure.
- `fixedFieldIntegersIsHenselian F` gives the Henselian local ring.
- With the residue algebra induced by `residueToFixedField F`,
  `fixedFieldResidueIsAlgClosure F` makes the residue field an algebraic
  closure of `𝓀[F]`. It is therefore algebraically closed and separably
  closed.

`M.isSmooth_baseChange` gives smoothness of `M.baseChangeUnramified`.
The published theorem `smoothHomExtension` then applies to the two
base-changed models and to the actual base change of `f`. Its point
hypothesis is precisely the supplied unramified integral-point
hypothesis. The abbreviations `baseMap` and `baseChanged` agree
definitionally with the spectrum map and group-scheme base change used
by the coefficient-base-change API.

## Descending the actual homomorphism

The application produces a homomorphism of the supplied models over
`fixedFieldIntegers F`, with the prescribed generic map over
`inertiaFixedField F`. The inverse of
`IntegralModel.Hom.valuationCoefficientEquiv`, for
`ValuativeRel.valuation F` and `fixedFieldValuation F`, descends this
homomorphism to `M.Hom N f`. This published equivalence supplies descent
along the canonical valuation-integer fpqc map and automatic generic
compatibility; no additional descent datum is assumed.

This is an internal composition of the published strictly Henselian
extension theorem, maximal unramified arithmetic, smooth base change,
and valued coefficient descent. It proves the local-field form using
the source's maximal-unramified integral points and assumes no
smoothness, reducedness, connectedness or reductivity of `N` or `H`.
The original statement pair and its imports are unchanged.
