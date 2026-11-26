# Root bounds for tempered twisted self-pairs

`TemperedSelfPairEulerRootRegionStatement.{u,uV}` takes an actual irreducible
analytically tempered action `ρ` of a positive-rank general linear group over a
bundled p-adic field with its canonical topology. Given an open-kernel character
`χ` of the general linear group with values of modulus one, the two pairs are
`(ρ, χρ∨)` and the pair of their smooth duals. Each certified Rankin–Selberg
polynomial for either pair is nonvanishing on the open unit disk. The additive
character and its self-dual measure are arbitrary.

`temperedSelfPairEulerRootRegion` uses `IsTempered.smoothContragredient` for the
first smooth dual and derives its irreducibility using the cofinal compact open
subgroups. `isTemperedModCenter_unitaryTwist` gives temperedness after twisting
for each Haar measure on the central quotient. Pair-polynomial uniqueness then
identifies the supplied forward denominator with the pole-free polynomial in
`analyticTemperedLPolynomialData`. To treat the dual pair, the equivalence
`smoothContragredientTwistEquiv` writes `(χρ∨)∨` as the twist of `(ρ∨)∨` by
`χ⁻¹`. The inverse character has the same open kernel and values of modulus one,
so the same argument applies starting with `ρ∨`.

For a norm-trivial twist used in the local self-pair identity, the determinant
character has open kernel and values of modulus one. The square-integrable
lower action is tempered, and the upper action is tempered by the definition of
`IsSigmaDiscreteSeries`. This is the root bound used in the comparison once
forward and reflected Euler factors are expressed in one residue variable.
The provenance is composition of the Library's actual tempered polynomial and
smooth duality results, following the separation step of Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique non nulle*
(2011), II.6.19, printed pp. 133–134 (PDF pp. 141–142), retained source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
