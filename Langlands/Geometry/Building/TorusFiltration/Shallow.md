# The minimal congruent torus subgroup at depths below one

Let `K = inertiaFixedField F` and `O = fixedFieldIntegers F` for a
nonarchimedean local field `F`. For a `K`-torus `T`,
`Langlands.Geometry.Building.minimalCongruentShallowSubgroup` gives a subgroup
of `T(K)` at each nonnegative real depth below one. At zero the subgroup
is the integral-point image of `connectedNeronModel`, equal to the
norm-defined Iwahori `T(K)^0`. At a positive depth the construction joins
the image of the first congruence kernel of the connected Néron model
with the images of `R(K)^std_r` under every `K`-homomorphism `R → T` from
an induced `K`-torus.

`inducedTorusStandardImages` uses a subgroup supremum over the actual
commutative group schemes satisfying `IsInducedTorus` and all the
indicated morphisms. The permutation-basis definition of
`IsInducedTorus` gives the finite products of Weil restrictions in the
source by `inducedTorusWeilDecomposition`. For each induced torus,
`localTorusFiltrationAtSplitting_eq_geometric_of_induced` identifies its
standard subgroup at positive depth with
`localGeometricCharacterCongruence`, the character congruences in the common
separable closure using the base-field normalization.

The subgroups lie in the Iwahori and contain the first congruence subgroup.
They decrease as depth increases. A morphism between tori preserves the
Iwahori by norm naturality and hence extends to the connected Néron models
by `IntegralModel.smoothHomExtension`. Reduction commutes with this
extension. Composition of morphisms carries each induced generator into a
generator for the target.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See Proposition B.3.6(1) and Definition B.5.1 for standard depths
(printed pp. 658–659 and 667 / PDF pp. 689–690 and 698), and
Definition B.10.8(1)–(2) and Proposition B.10.10 for the construction
and its functoriality at these depths (printed p. 690 / PDF p. 721).
The clarification specifying induced `K`-tori is in
`kaletha-prasad-2024-corrections`, version of 1 November 2024, PDF p. 50,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
