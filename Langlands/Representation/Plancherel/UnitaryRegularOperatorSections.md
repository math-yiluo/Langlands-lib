# Smooth orbit sections from regular operators

This module collects generic steps for building an actual smooth orbit section whose compact
picture is a regular operator applied to another smooth family.

## Regular operators on finite smooth families

Let `e` be circle coordinates of the unitary unramified characters with Laurent evaluations
(`HasLaurentUnitaryCoordinates`). Let `d` be a regular function nonzero at every unitary character
and `A` an operator family polynomial on every fixed vector (`IsPolynomialOperatorOn`).

- `unitaryRegularOperator_mem_finiteSmoothFamilies`: for a finite smooth family `R`,
  `z ↦ d(z)⁻¹ A(z) (R z)` (`unitaryRegularOperator`) is a finite smooth family. Expand `R` as
  `Σ f_i(z) v_i` and each `A(z) v_i` as `Σ b_ij(z) w_ij`. The scalars `f_i · d⁻¹ · b_ij` are smooth by
  `isSmoothFiniteTorusFunction_unramifiedRegularFunction`, with the inverse smooth since `d` has no
  zero on the torus.
- `unitaryRegularOperator_comp_monomial_mem_finiteSmoothFamilies`: the same after the change of
  coordinates by an integer monomial `finiteTorusMonomial a`
  (`mem_finiteSmoothFamilies_comp_monomial`).

## Covariance by the identity principle

For a translation `τ` of unramified characters:

- `isPolynomialOn_mul_translate` and `isPolynomialOn_regular_mul_translate_smul`: translating a
  polynomial family, or multiplying it by a translated regular function, preserves polynomiality
  (`unramifiedRegularTranslation`).
- `mul_mem_interior_of_forall_mul_mem`: if `D` is stable under translation by `τ`, so is its
  interior.
- `regular_smul_mul_eq_of_isOpen`: let `N = d · c` on the interior `D°` of the domain of a family
  `c`, with `N` polynomial and `D°` nonempty and stable under `τ`. Let `P`, `Q` be linear maps with
  `c(zτ) ∘ P = Q ∘ c(z)` whenever `z, zτ ∈ D`. If polynomial families vanishing on a nonempty
  open set vanish everywhere (hypothesis `hId`), then `d(z) N(zτ)(P X) = d(zτ) Q(N(z) X)` for all `z`
  and `X`. The difference is a polynomial family that vanishes on `D°`.
- `regular_inv_smul_mul_eq_of_isOpen`: hence `d(zτ)⁻¹ N(zτ)(P X) = Q(d(z)⁻¹ N(z) X)` wherever
  `d(z)` and `d(zτ)` are nonzero.

## Compact self-twist operators

`productCompactSelfTwistEquiv_eq_of_eq`: for an admissible irreducible inducing representation,
the compact self-twist operators (`productCompactSelfTwistEquiv`) of two self-twists by equal
characters coincide. After substituting the equality, this is Schur's lemma in the form
`productCompactSelfTwistEquiv_independent`.

## Sections with a prescribed compact picture

`exists_productInducedSmoothOrbitSection`: let `Fc` be a finite smooth family of compact pictures
with `Fc(z · s) = s · Fc(z)` for every `s` in the unitary class stabilizer, where `s ·` is
`unitaryStabilizerCompactRepresentation`. Then there is an actual smooth orbit section
(`productInducedSmoothOrbitSections`) whose parameter pullback has compact restriction `Fc`. The
inverse of the compact restriction gives an element of `productInducedSmoothFamilies`
(`finiteSmoothEquivariantFamilies`). `productInducedSmoothOrbitExtension` extends it to all
orbit representatives, and `productInducedOrbitPullback_extension` recovers the family.

## Source

These are derived steps for the smooth sections `sω ↦ c̃_{P'|P}(s, ω) q_ω` used by J.-L.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), printed p.304 (registered as `waldspurger-2003-plancherel`,
SHA-256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). There
`sp_χ c̃_{P'|P}(s) ψ` is written as a finite sum `Σ φ_{ψ'}(sχ) sp_{sχ} ψ'` with smooth coefficients
`φ_{ψ'}` on `Im X(s·M)`. The first section above gives such a finite expansion for a regular
operator. The identity principle is a hypothesis of the covariance lemmas here. For the standard
Levi subgroups it is the Library's `leviPolynomial_eq_zero_of_isOpen`.
