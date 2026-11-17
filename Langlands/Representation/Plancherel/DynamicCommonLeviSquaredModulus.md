# Squared modulus for dynamic parabolics with a common Levi

This derived adapter supplies the squared-modulus premise of the published
`DynamicCommonLeviComposition.pairFamily` for two cocharacters of one maximal
split torus with equal dynamic centralizer. It is used in the construction of
Waldspurger's c-family in V.1, printed pp.288–289, in *La formule de Plancherel
pour les groupes p-adiques d'après Harish-Chandra* (2003). The squared-modulus
identity itself is an internal structural ingredient, rather than a separate
assertion at that source location.

The field and all group schemes have universe `u`. The modulus theorem uses
an arbitrary nonarchimedean local field, with no restriction on its
characteristic. There is no representation parameter. Rational points have
their canonical topology. The measurable and Borel structures on the actual
radical intersection, as a subgroup of the second radical, remain explicit;
these are the same structures needed by `pairFamily`.

Fix an ambient cocharacter `χ`, a maximal split torus `i : T ⟶ G`,
and cocharacters `ζ, η` of `T` with

\[
Z_G(\zeta)=Z_G(\eta)=Z_G(\chi).
\]

These are equalities of subgroup functors on all test schemes. The common
Levi in the resulting standard integral is the literal subgroup
`levi χ` of `G(F)`, and its scheme representative is the existing
`parameterScheme χ`.

`torusParameterFactor χ i ζ hζ` factors `T` through that actual parameter
scheme, using the published `Dynamic.torusFactor` and the given centralizer
equality. Its composite with the centralizer inclusion equals `i`.
`torusParameterFactor_characterRestrict_injective` proves that rational
characters of the parameter scheme restrict injectively to this torus,
assuming `CentralSplitTorusCharacterStatement` and connected reductivity of
`G`. Indeed, a nonzero character is detected on a central split torus by that
statement; the published central-split-torus factorization factors this
detecting torus through `torusParameterFactor`. A character restricting to zero
on `T` would then restrict to zero on the detecting torus, a contradiction.
Connected reductivity of the parameter scheme is the published theorem
`parameterScheme_isConnectedReductive`.

`squaredModulus_of_centralSplitTorusCharacter` proves exactly
`SquaredModulusCompatibility` for the two existing `commonDecomposition`
values and their closed radical inclusions. In ambient Haar characters, its
content is

\[
\delta_{U(\zeta)}(m)\,\delta_{U(\eta)}(m)
  =\delta_{U(\zeta)\cap U(\eta)}(m)^2,\qquad m\in Z_G(\chi)(F).
\]

The proof uses the published actual affine representatives of the two
radicals and their intersection, with the existing finite Lie-coordinate
construction. The relative root system premise is discharged by the proved
`relativeRootSystem`, applied to `i`. The published
`centralizingHaarCharacter_values_square_of_centralizer_eq`, with the
injectivity above, gives the displayed identity on the actual parameter
scheme. Every point of `levi χ` lifts to that scheme by its representing
property. Congruence of closed-normalizer Haar characters then identifies
the identity with the premise of `pairFamily`, using the published
`squaredModulusCompatibility_iff`.

The only structural proposition retained as a parameter is
`CentralSplitTorusCharacterStatement`. Connected reductivity and maximal
splitness are hypotheses on the supplied actual data. No root-system
statement, modulus identity, expansion, regularity, finite decomposition,
packet identity or coefficient bound is assumed.
