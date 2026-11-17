# Locally constant character maps of split torus homomorphisms

This internal derived unit proves the first step of Conrad, *Reductive group
schemes* (2014), Proposition 6.1.7, over an affine base `Spec R`. A homomorphism
`τ : 𝔾_m^I → 𝔾_m^{I'}` of coordinate split tori acts on character lattices
through a linear map that is locally constant on `Spec R`. Conrad states this on
p.187, before Lemma 6.1.3: "There is an open cover {U_i} of S such that the map
induced by X(f) on U_i-sections carries M into M′." Here the statement is proved
directly from the group-like elements of the coordinate ring `R[ℤ^I]`, and the
open sets are basic open sets of idempotents of `R`.

## The predicate

`splitTorus.CharacterMapOn τ V h` is a definition. Its arguments are an open set
`V` of `Spec R` and a `ℤ`-linear map `h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)`. It states the
following for every test scheme `U` over `Spec R` whose structure morphism maps
`U` into `V` (`U.hom ⁻¹ᵁ V = ⊤`), every point `x` of `𝔾_m^I` over `U`, and every
exponent vector `m : I' → ℤ`:

`∏ j', (τ x)_{j'} ^ m j' = ∏ j, x_j ^ (h m) j`.

Here `x_j` and `(τ x)_{j'}` are the unit coordinates given by
`splitTorus.pointsEquiv`. In words, over `V` the map `τ` pulls the exponent
character `m` of `𝔾_m^{I'}` back to the exponent character `h m` of `𝔾_m^I`.
This is the form of the character-map clause in
`AffineSplitSurjectionRootDatumStatement`.

## Construction

`diagIso` is the Library's coordinate identification of the diagonalizable group
`D(ℤ^I)` with the split torus `𝔾_m^I`. For each `j' : I'`,
`coordinateUnits τ j'` is the `j'`-th coordinate of `τ`, viewed as a
`DiagonalizableCharacter.NaturalUnits` family on `D(ℤ^I)`. That is, it is a
homomorphism from the points to the units of sections, natural in the test
scheme. Its value `v_{j'}` in the coordinate ring `R[ℤ^I]` is group-like by the
Library theorem `NaturalUnits.isGrouplike_value`. Hence its coefficients are
orthogonal idempotents with sum `1`. `characterPointsEquiv_diag` states that,
under `diagIso`, the characters of `D(ℤ^I)` are the exponent monomials in the
split coordinates.

`algebraMap_sections` records that `R` maps to the global sections of a test
scheme through its structure morphism. The proof is `rfl`. `lift_eq_of_coeff`
considers an element `v` of `R[Λ]` whose coefficients become `δ_{n,M}` in an
algebra `B`. It shows that evaluating `v` at a character `χ` gives `χ(M)`.

## Main theorem

`exists_isIdempotentElem_characterMapOn` states: for every point `s` of
`Spec R`, there are an idempotent `e : R` with `s` in the basic open set
`D(e)` (written `(Spec R).basicOpen ((Scheme.ΓSpecIso R).inv e)`) and a linear
map `h` such that `CharacterMapOn τ D(e) h` holds.

Proof. The coefficients of `v_{j'}` sum to `1`, so for each `j'` some
coefficient `c_{j'} = v_{j'}(M j')` lies outside the prime `s`. Put
`e = ∏ c_{j'}`. It is idempotent and lies outside `s`. Let
`h = Fintype.linearCombination ℤ M`, the linear map sending the `j'`-th basis
vector to `M j'`. Take a test scheme `U` mapping into `D(e)`. The image of `e`
in `Γ(U)` is a unit, by the private lemma `isUnit_of_basicOpen_eq_top'`.
Idempotents dividing a unit equal `1`, so every `c_{j'}` maps to `1` in `Γ(U)`.
By orthogonality, every other coefficient of `v_{j'}` maps to `0`. Thus
`lift_eq_of_coeff` shows that the `j'`-th coordinate of `τ x` is the character
`M j'` of `x`. Taking the product of the `m j'`-th powers gives the character
`h m`.
