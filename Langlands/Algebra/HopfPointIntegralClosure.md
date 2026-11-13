# Bialgebra maps into group algebras: surjectivity and integral coefficients

This module provides the two algebraic facts behind the split-torus closure
lemma `Langlands.GroupScheme.IntegralModel.SplitTorusClosure`. Both are internal
deductions; see "Provenance" below for how they relate to Kaletha–Prasad.

## Surjectivity of bialgebra maps into a group algebra

Let `R` be a commutative ring, `B` a commutative `R`-bialgebra, `M` an additive
commutative group, and `φ : B →ₐc[R] R[M]` a bialgebra map. Here `R[M]` is
`AddMonoidAlgebra R M` with its group-like comultiplication.

* `coeffIdeal φ m` is the ideal of `R` given by the range of the linear map
  `b ↦ (φ b).coeff m`. `coeff_mem_coeffIdeal` records the obvious membership.
* `coeffPair m : R[M] ⊗[R] R[M] →ₗ[R] R` multiplies the degree-`m` coefficients
  of the two tensor factors (`coeffPair_tmul`). `coeffPair_comul` shows that
  `coeffPair m (Δ x) = x.coeff m`. The proof uses linear induction on `x`; a
  monomial `single n r` has comultiplication `single n r ⊗ single n 1`.
* `coeffIdeal_le_mul`: `φ` commutes with comultiplication, so
  `(φ b).coeff m = coeffPair m ((φ ⊗ φ)(Δ b))`. Expanding `Δ b` into pure
  tensors places this in `coeffIdeal φ m * coeffIdeal φ m`. Hence
  `isIdempotentElem_coeffIdeal`: each coefficient ideal is idempotent.
* `coeffIdeal_eq_top`: Let `R` be a noetherian domain. Each coefficient ideal is
  finitely generated and idempotent, so Mathlib's
  `Ideal.isIdempotentElem_iff_eq_bot_or_top` makes it `⊥` or `⊤`. If some
  `(φ b).coeff m` is nonzero, the ideal is `⊤`.
* `surjective_of_coeff_ne_zero`: Let `R` be a noetherian domain. If for every
  degree `m` some `b` has `(φ b).coeff m ≠ 0`, then `φ` is surjective. The
  proof picks `b` with `(φ b).coeff m = 1`. The published
  `DiagonalCoalgebraImage.single_coefficient_mem_range` then puts the monomial
  `single m 1` in the range. The published
  `DiagonalCoalgebraLocus.surjective_of_generators_mem`, applied to the
  generating set `Set.univ`, concludes.

## Laurent polynomials evaluated at units

Let `I` be a finite type. Write `R[ℤ^I]` for `AddMonoidAlgebra R (I → ℤ)`.

* `unitChar t` sends an `I`-indexed family `t` of units of a commutative monoid
  `B` to the character `m ↦ ∏ᵢ tᵢ ^ mᵢ` of `Multiplicative (I → ℤ)` with values
  in `Bˣ`. `unitChar_map` shows that it commutes with monoid homomorphisms.
* `evalUnits R t : R[ℤ^I] →ₐ[R] B` evaluates a Laurent polynomial at a family
  `t` of units of an `R`-algebra `B`. `evalUnits_single` and `evalUnits_apply`
  give its values. `evalUnits_mapRingHom` gives naturality in a ring
  homomorphism `f : A →+* B`, applied to the coefficients and to the units.
  `evalUnits_mapRingHom_algebraMap` says that, for a `K`-algebra `L`,
  evaluating at units of `L` commutes with extending coefficients from `K` to
  `L`.
* `mem_range_mapAlgHom_of_coeff`: Let `R → K` be an algebra map. A Laurent
  polynomial over `K` whose coefficients all lie in the image of `R` lies in the
  range of the coefficient extension `R[ℤ^I] → K[ℤ^I]`.
* `evalChar k m : (I → kˣ) →* k` is the character `t ↦ ∏ᵢ tᵢ ^ mᵢ` of
  `(kˣ)^I`, for a field `k`. `evalChar_injective` shows that distinct exponents
  give distinct characters when `k` is infinite. If `mᵢ ≠ m'ᵢ`, choose a nonzero
  `u` that is not a root of unity of order `|mᵢ - m'ᵢ|`, then test on the family
  that is `u` at `i` and `1` elsewhere.
* `eq_zero_of_forall_evalUnits_eq_zero`: over an infinite field, a Laurent
  polynomial that vanishes at every family of units is zero. This follows from
  Mathlib's linear independence of characters (`linearIndependent_monoidHom`)
  composed with `evalChar_injective`.
* `coeff_mem_range_of_forall_evalUnits_mem`: Let `A` be a valuation ring that is
  a domain, with fraction field `K` and infinite residue field. If a Laurent
  polynomial `P` over `K` takes values in `A` at every family of units of `A`,
  then every coefficient of `P` lies in `A`. Write `v` for
  `ValuationRing.valuation A K` and assume `P ≠ 0`. Choose a coefficient `c` of
  `P` of maximal valuation, and divide all coefficients by `c`. The quotients
  are integral, and the one in degree `m₀` (the degree of `c`) equals `1`.
  Their reduction `Q` to the residue field is therefore a nonzero Laurent
  polynomial. By the previous lemma, some family of residue units `t̄` has
  `Q(t̄) ≠ 0`. Lift `t̄` to units `t` of `A`. Then `P(t) = c · E`, where `E ∈ A`
  reduces to `Q(t̄)` and so is a unit. Since `P(t)` is integral, `c` is
  integral, and every coefficient has valuation at most `v c ≤ 1`.

## Provenance

These results serve the closure statement for split tori (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, 2023, Lemma B.2.3 and Proposition B.2.4,
printed pp. 655–656). The Lean route differs from the book.

* KP prove the implication (1)⇒(2) of Lemma B.2.3 with the smoothening and a
  weight decomposition. The coefficients `aₓ` of the affine ring satisfy
  `aₓ² ∣ aₓ`, so they are units. `surjective_of_coeff_ne_zero` instead uses
  idempotent coefficient ideals over a noetherian domain. It assumes neither
  smoothness nor a weight decomposition.
* KP pass from integral points to integrality of the model through Lemma B.2.3
  and the smoothening. `coeff_mem_range_of_forall_evalUnits_mem` gives a direct
  argument for split tori instead: it evaluates at integral units, which needs
  an infinite residue field.

No further literature assertion is used.

Drafted by Worker 5707 for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`, shared draft revision 2). The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
