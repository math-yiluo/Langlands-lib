# The grading of the coordinate ring of a dynamic unipotent subgroup

Namespace `Langlands.GroupScheme.Corepresented`. Let G = Spec B be a
corepresented affine group over Spec R, R any commutative ring, and let
χ : 𝔾ₘ → G be a cocharacter. The Library represents the dynamic unipotent
subgroup U_G(χ) by Spec (B ⧸ J), where J = `unipotentIdeal χ`
(`Corepresented.unipotentScheme χ`). This module shows that the conjugation
coaction of χ descends to a grading of B ⧸ J, with no components of negative
degree and with scalars in degree zero. It also proves the identity that
connects conjugation of points of U_G(χ) with this grading.

## Provenance

These are internal helper results for the local-ring Isomorphism Theorem task
(ab10ec3c). The grading is the standard ℤ-grading of the coordinate ring of an
affine scheme with a 𝔾ₘ-action, here for the conjugation action of χ. Conrad,
*Reductive group schemes* (2014), Theorem 4.1.7 and its proof (printed
pp.112–113) uses it to construct U_G(λ). The proofs use the Library's coaction
lemmas (`Corepresented.coaction_algebraMap`, `sum_coeff_coaction`,
`coaction_coeff_coaction`) and the Library's conjugation formula
`Corepresented.pointRing_conj`.

## The grading

- `unipQuot χ` is the quotient map B → B ⧸ J. `reducedCoaction χ` is the
  coaction followed by reduction of coefficients modulo J.
- `reducedCoaction_of_homogeneous` and `unipotentIdeal_le_ker`: the generators
  of J are homogeneous elements of J. These are the coefficients of negative
  degree c(b)ₙ, and the differences c(b)₀ − ε(b) with ε the counit. Hence J lies
  in the kernel of `reducedCoaction χ`.
- `unipCoaction χ` is the induced map B ⧸ J → (B ⧸ J)[T, T⁻¹].
  `unipCoaction_mk` and `coeff_unipCoaction_mk` compute it on classes.
- `isGrading_unipCoaction`: it is a grading in the sense of
  `CommutativeAlgebra.GradedLine.IsGrading`.
- `unipCoaction_coeff_neg`: there are no components of negative degree, since
  the negative coefficients are generators of J.
  `unipCoaction_coeff_zero`: the degree-zero component of the class of b is the
  scalar ε(b).

## Points and conjugation

- `pointRing_unipotentHom`: the classifying map of a point of U_G(χ), viewed in
  G, is the quotient map followed by its classifying map. This uses the
  Library's `cutHom_left`.
- `unitT D` is the unit T of D[T, T⁻¹], with `unitT_zpow`: T^n is the Laurent
  monomial of degree n. `eval₂_T_mapRingHom`: evaluating at T a Laurent
  polynomial whose coefficients are made constant recovers the Laurent
  polynomial itself.
- `constIncl` is the constant inclusion K[X] → K[X][T, T⁻¹], for a field K over
  R.
- `scaling_of_conj`: let y₀ be a point of U_G(χ) over Spec K[X] and y₁ a point
  over Spec K[X][T, T⁻¹]. Suppose y₁ is classified by the classifying map ψ of y₀
  followed by X ↦ T^m X. Suppose further that conjugating the pullback of y₀ by
  χ(T) gives y₁. Then ψ intertwines the grading with the scaling:
  `mapRingHom ψ (unipCoaction χ a) = aeval (T^m X) (ψ a)` for all a. The proof
  applies `pointRing_conj` to the conjugation identity. It then uses
  `pointRing_unipotentHom` and `eval₂_T_mapRingHom`, and evaluates at a class
  π(b). By `CommutativeAlgebra.GradedLine.coeff_eq_zero_of_scaling`, this
  identity makes ψ graded.

All results use only the standard axioms.

The ring-algebra point helpers used here are from
`Langlands.GroupScheme.Corepresented.RingCoordinates` in
`Langlands.GroupScheme.Dynamic.RingPointCoordinates`.
