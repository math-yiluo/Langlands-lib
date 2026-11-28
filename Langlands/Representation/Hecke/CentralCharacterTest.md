# Locally constant tests with a prescribed central character

Henniart and Lemaire, *Changement de base et induction automorphe pour
GL_n en caractéristique non nulle* (2011), I.2.9–I.2.10, printed pp. 22–23
(PDF pp. 30–31), introduce the space of tests and its linear averaging map.
The retained PDF has source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
The same convention is used in II.2.6–II.2.7, printed pp. 66–67 (PDF pp. 74–75).

`Langlands.Hecke.CentralCharacterTest Z ω` is the complex vector space of
locally constant functions on a topological group `G` whose nonzero set has
compact image in the quotient group `G ⧸ Z`. The character is locally constant
and circle-valued. The defining rule is `q(z g) = ω(z)⁻¹ q(g)`. Requiring a unitary
character specializes the character convention in I.2.9. The projected support
is clopen because the nonzero set is clopen and saturated. The construction of
the space works for any normal subgroup. The averaging construction uses a
closed central subgroup.

For a locally compact Hausdorff totally disconnected group and a closed central
subgroup `Z`, `CentralCharacterTest.average` sends a Library `SchwartzBruhat G`
test `f` to the function with value `∫ z, ω(z) f(z g) dz` at `g`, using the
supplied Borel Haar measure `dz`. The closed subgroup fiber meets the support of
`f` in a compact set. The continuous weighted integrand is therefore integrable.
A compact open subgroup fixing `f` on the right fixes the average on the right,
giving local constancy. Right translation of the integration variable in the
central subgroup gives the inverse character law. The projected support is
contained in the compact image of the support of `f`, and its closedness gives
compactness. Pointwise integral addition and scalar multiplication give the
complex-linear map.
