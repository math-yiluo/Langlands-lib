# A finite group attached to a representation that is scalar on a finite-index subgroup

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`.
It follows the finite-group construction in item 3 of "Relation to the source"
in the Markdown of the statement module
`Langlands.VirtualRepresentation.Global.RelativeWeilInductionGenerationStatement`:
there, `H₀ = G ∩ SL(V_η)`, where `G = ρ(W_H)·ℂ^×`. This module states and
proves the algebraic part of that construction for any group `S` and any
complex representation `ρ : Representation ℂ S V`. No topology is used. All
declarations are in the namespace `Langlands.VirtualRepresentation.ScalarKernel`.

## The normalized image

- `normalizedImage ρ` is the subgroup of `(Module.End ℂ V)ˣ = GL(V)` of units
  `h` with `det h = 1` and `h = z • ρ s` for some `s : S` and `z : ℂˣ`. Closure
  under products and inverses follows from `ρ (s t) = ρ s * ρ t` and
  `ρ s⁻¹ = (ρ s)⁻¹`. `endOf ρ h` is the underlying endomorphism of `h`.
- `tautological ρ` is the representation of `normalizedImage ρ` on `V` by
  `h ↦ endOf ρ h`.
- `exists_pre`, `preElem`, `preScalar` and `pre_spec`: every `h` satisfies
  `ρ (preElem ρ h) = preScalar ρ h • endOf ρ h`, for a chosen element of `S`
  and a chosen unit scalar.
- `commute_of_scalar`: an element `h` with `endOf ρ h = c • 1` commutes with
  every element of the normalized image.
- `scalar_of_smul_eq`: if `c₁ • h₁ = c₂ • h₂` in `End V`, then `h₁ h₂⁻¹` is the
  scalar `(c₂ / c₁) • 1`.

Assume now that `V` is nontrivial (and, from `exists_lift` on,
finite-dimensional).

- `det_ne_zero`: `det (ρ s) ≠ 0`, since `ρ s` is invertible.
- `scalar_ne_zero`: if `ρ s = c • 1` then `c ≠ 0`.
- `exists_lift`, `liftScalar`, `liftElem` and `lift_spec`: every `ρ s` equals
  `liftScalar ρ s • endOf ρ (liftElem ρ s)` with `liftElem ρ s` in the
  normalized image. Take a `d`-th root `w` of `det (ρ s)`, where
  `d = finrank V > 0` (`IsAlgClosed.exists_pow_nat_eq`). Then `w⁻¹ • ρ s` is a
  unit of determinant `w^{-d} · det (ρ s) = 1`.
- `finite_normalizedImage ρ N hN`: if `N` has finite index in `S` and every
  `ρ n` (`n ∈ N`) is a scalar, then the normalized image is finite. Write
  `s = q.out · n⁻¹` with `q` the coset of `s` in `S ⧸ N` and `n ∈ N`. If
  `h = z • ρ s` has determinant one, then `h = w • ρ q.out`, where
  `w^d · det (ρ q.out) = 1`. So `endOf ρ h` lies in the finite union over the
  finitely many cosets `q` of the images of the root sets of the nonzero
  polynomials `C (det (ρ q.out)) · X^d − 1` (`Polynomial.finite_setOfPred_isRoot`).
  `Units.val` is injective, so this gives finiteness.

## The tautological part and the scalar lift

Let `σ` be a representation of the normalized image on a complex vector space
`Y`.

- `tautPart ρ σ` is the subspace of `y` with `σ h y = c • y` whenever
  `endOf ρ h = c • 1`. On it every scalar element `c • 1` acts by `c`.
  `tautPart_stable`: it is stable under every `σ k`, because scalar elements
  are central.
- `tautPart_key`: on the tautological part, `c₁ • h₁ = c₂ • h₂` in `End V`
  implies `c₁ • σ h₁ y = c₂ • σ h₂ y`. The proof writes
  `h₁ = (h₁ h₂⁻¹) h₂` and uses `scalar_of_smul_eq`.
- `tautPart_tautological`: the tautological part of `tautological ρ` is all of
  `V`.
- `scalarLift ρ σ : Representation ℂ S (tautPart ρ σ)`. The element `s` acts by
  `liftScalar ρ s • σ (liftElem ρ s)` restricted to the tautological part.
  `scalarLift_of_eq` (and `scalarLiftFun_of_eq`): for any decomposition
  `ρ s = c • endOf ρ h`, `s` acts by `c • σ h`, by `tautPart_key`. This gives
  `map_one` and `map_mul`: `ρ (s t) = (z_s z_t) • (h_s h_t)`.

## Functoriality

- `equiv_apply`: the pointwise form `e (σ g v) = σ' g (e v)` of an equivalence
  of representations.
- `tautPartLinearEquiv e` and `scalarLiftEquiv ρ e`: an equivalence `e` of
  representations of the normalized image restricts to the tautological parts
  and gives an equivalence of the scalar lifts.
- `tautPartProdLinearEquiv` and `scalarLiftProdEquiv`: the scalar lift of a
  product representation is equivalent to the product of the scalar lifts.
- `scalarLiftTautologicalEquiv ρ`: the scalar lift of `tautological ρ` is
  equivalent to `ρ`. Indeed `s` acts by `z_s • h_s = ρ s`.

## Dependencies

The module imports `Langlands.Weil.Representation.Predicates` and Mathlib
(polynomial roots, the algebraic closedness of `ℂ`, determinants and traces).
