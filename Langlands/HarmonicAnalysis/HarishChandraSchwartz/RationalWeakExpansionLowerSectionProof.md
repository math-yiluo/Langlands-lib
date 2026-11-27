# Lower sections of the weighted c-family

This module proves `weightedCLowerSection`, the statement `WeightedCLowerSectionStatement` of the
module `RationalWeakExpansionIdentityInputs`. Fix a Weyl index `s`, a rational extension `E` of
the weighted c-family `c̃_{P'|P}(s, ·)` (`WeightedCExtension`) and a section `q ∈ C^∞(O, P)`
(`rationalInducedSmoothOrbitSections`). There is a lower smooth section
`Ψ ∈ C^∞(sO, M' ∩ s·P)` (`LowerSections`) with `IsWeightedCSection E q Ψ`. This means that at
every unitary character `z` of `M_I(F)` the compact picture of `Ψ` at the conjugate character `sz`
is the value `E.unitaryValue z` applied to the compact picture of `q` at `z`.

The general form is `exists_isWeightedCSection`, for one normalizer lift `n` with `s·M ⊆ M'`, one
lower density package and the common compact normalization. `weightedCLowerSection` applies it to
`R.normalizer s` for every `s`. The proof does not use the square integrability of `π`, the
properness of `I'` or the special compact hypothesis of the statement; it uses only `E`.

## The lower compact family

Write `e : M_I(F) ≃ s·M(F)` for the Weyl conjugation `lowerLeviConjugation` and
`lowerCharacterConjugation` for `z ↦ z ∘ e⁻¹` on unitary unramified characters. For circle
coordinates `w` of `Im X(s·M)` (`DynamicInducedOrbit.leviUnitaryCoordinates`) put
`z(w) = lowerCharacterConjugation⁻¹ (w)`, read through those coordinates. Then

`lowerCompactFamily E q w = E.unitaryValue (z(w)) (sectionCompactPicture q (z(w)))`.

At `w` equal to the coordinates of `lowerCharacterConjugation z`, `z(w) = z`, so a section whose
compact picture is this family satisfies `IsWeightedCSection E q`. Two properties remain.

## Smoothness

`lowerCompactFamily_mem_finiteSmoothFamilies` shows that the family is a finite smooth family on
the torus of `Im X(s·M)`. By `exists_monomial_lowerCharacterConjugation_symm` (module
`RationalWeakExpansionLevelControl`), the upper circle coordinates of `z(w)` are an integer
monomial `finiteTorusMonomial a w`. At these coordinates the value of `E` is the regular operator
`d⁻¹ N` of its denominator and numerator (`unitaryRegularOperator`), applied to the compact
picture of `q`. That compact picture is a finite smooth family by the definition of
`C^∞(O, P)`. The numerator is polynomial and the denominator vanishes at no unitary character
(`WeightedCExtension.polynomial`, `WeightedCExtension.unitary_regular`).
`unitaryRegularOperator_comp_monomial_mem_finiteSmoothFamilies` (module
`UnitaryRegularOperatorSections`) then gives smoothness.

## Covariance

`lowerCompactFamily_mul_stabilizer` shows that
`lowerCompactFamily E q (w · σ) = σ · lowerCompactFamily E q w` for every `σ` in the unitary
stabilizer of the class of `sπ` (`lowerRepresentation`). Here `σ ·` is the stabilizer operator
`unitaryStabilizerCompactRepresentation` on the lower compact picture. The proof has four steps.

1. `lowerCharacterConjugation_symm_mem_stabilizer`: `τ = σ ∘ e` stabilizes the class of `π`.
   A self-twist of `sπ` by `σ` has the same linear map as a self-twist of `π` by `τ`
   (`upperSelfTwist`). Since `z(w · σ) = z(w) τ`, the family at `w · σ` is evaluated at `z(w) τ`.
2. `sectionCompactPicture_mul_stabilizer`: the compact picture of `q` at `z τ` is the stabilizer
   operator of `τ` applied to that at `z`. This is the covariance in the definition of the
   smooth families (`productInducedSmoothOrbitPullback`).
3. `unitaryValue_mul_selfTwist`: for unitary `z`, `τ` and a self-twist `a : π ≃ π ⊗ τ`,
   `E.unitaryValue (z τ) ∘ a = (s a) ∘ E.unitaryValue z` on the compact pictures, where `s a` is the
   lower self-twist `lowerSelfTwist`. On `cWeightedDomain` the weighted family itself has this
   covariance (`cWeightedCompactFamily_selfTwist`, module
   `RationalWeakExpansionWeightedCovariance`). That domain is stable under translation by `τ`
   (`mul_mem_cWeightedDomain_selfTwist`), hence so is its interior
   (`mul_mem_interior_of_forall_mul_mem`). On the interior the numerator is `d · c̃`, so the
   polynomial family `d(z) N(zτ)(a X) − d(zτ) (s a)(N(z) X)` vanishes on a nonempty open set.
   The identity theorem `leviPolynomial_eq_zero_of_isOpen` makes it vanish everywhere
   (`regular_smul_mul_eq_of_isOpen`). Dividing by the denominators, nonzero at unitary
   characters, gives the identity (`regular_inv_smul_mul_eq_of_isOpen`).
4. `lowerSelfTwist_eq_stabilizer`: the lower self-twist operator of `a` is the stabilizer
   operator of `σ`. The Weyl conjugation of `τ` is `σ`
   (`lowerUnramifiedCharacterConjugation_inclusion_symm`), and two self-twists by equal
   characters of the irreducible admissible `sπ` give the same compact operator
   (`productCompactSelfTwistEquiv_eq_of_eq`, from Schur's lemma through
   `productCompactSelfTwistEquiv_independent`).

## The section

`exists_productInducedSmoothOrbitSection` (module `UnitaryRegularOperatorSections`) turns the
smooth covariant family into an actual coherent smooth orbit section whose compact picture is
`lowerCompactFamily E q`. This is `exists_isWeightedCSection`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), registered as `waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), printed p.304. There, for
each `s`, Proposition V.1.1 and Corollary V.2.3 give a rational map `c̃_{P'|P}(s)` with
`χ ↦ sp_χ c̃_{P'|P}(s)` regular on `Im X(M)`. Waldspurger then writes `sp_χ c̃_{P'|P}(s) ψ` as a
finite sum `Σ φ_{ψ'}(sχ) sp_{sχ} ψ'` with smooth `φ_{ψ'}` on `Im X(s·M)`. That is, `sω ↦ c̃(s, ω) q_ω`
is a smooth section over the orbit `sO`. The module proves this for the Library's actual sections.
The covariance under the stabilizer, which an actual section over `sO` must satisfy, is derived
from the covariance of the weighted c-family on its domain and the identity theorem. Waldspurger
does not state it separately.
