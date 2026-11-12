# Similitude points over coefficient rings on which an imaginary quadratic field splits

Author: Worker 19.

This internal algebraic construction identifies the similitude points of a
rational involution of the second kind relative to an imaginary quadratic
field `L` over every commutative `L`-algebra `S`:

`σ.Points S ≃* (S ⊗[L] A)ˣ × Sˣ`.

It is the instance of `CentralExchangeSplitting` (submitted together with this
module) for the central idempotent of `S ⊗[ℚ] A` on which the two actions of
`L`, through `S` and through `A`, agree. The Harris specialization at a
`p`-adic completion is `HarrisSplitPrimePoints`.

## Setting

All declarations are in namespace `Langlands.Shimura.ImaginaryQuadraticSplit`.
`L` is a number field with `IsCMField L` and `Algebra.IsQuadraticExtension ℚ L`,
that is, an imaginary quadratic field; `conj` is Mathlib's
`IsCMField.complexConj L`. Some auxiliary results need fewer hypotheses and
`omit` the others.

## A generator of `L`

- `exists_complexConj_ne`: some `t : L` satisfies `conj t ≠ t`, because
  complex conjugation of a CM field is not the identity
  (`IsCMField.complexConj_ne_one`).
- `generator L` is such an element, chosen by `Classical.choose`;
  `complexConj_generator_ne` and `generator_sub_ne_zero` record
  `conj g ≠ g` and `g - conj g ≠ 0` for `g = generator L`.
- `exists_rat_combination`: every `t : L` is `a + b * g` with rational
  `a`, `b`, because `1` and `g` are linearly independent over `ℚ` (otherwise
  `g` would be rational, hence fixed by `conj`) and `L` has dimension `2`.

## The idempotent of a commutative ring with two maps from `L`

Let `Z` be a commutative ring and `i j : L →+* Z` ring homomorphisms.

- `idempotent i j = i ((g - conj g)⁻¹) * (j g - i (conj g))`.
- `ratCast_eq`: `i` and `j` agree on rational numbers.
- `inv_mul_self`: `i ((g - conj g)⁻¹) * i (g - conj g) = 1`.
- `generator_relation`: `(j g - i (conj g)) * (j g - i g) = 0`. Writing
  `g ^ 2 = a + b * g` with `a`, `b` rational, one gets `g + conj g = b` and
  `g * conj g = -a`; the product expands to `j g ^ 2 - b * j g - a`, which is
  `j (g ^ 2 - b * g - a) = 0`.
- `idempotent_mul_generator` and `idempotent_mul_apply`: for every `t : L`,
  `idempotent i j * j t = idempotent i j * i t`. So multiplication by the
  idempotent makes the two actions of `L` agree.
- `idempotent_mul_self`: `idempotent i j` is idempotent.
- `idempotent_conj`: if `j' t = j (conj t)` for all `t`, then
  `idempotent i j' = 1 - idempotent i j`.
- `idempotent_map`: if a ring homomorphism `φ : Z →+* Q` satisfies
  `φ (j t) = φ (i t)` for all `t`, then `φ (idempotent i j) = 1`.

## The tensor algebra

Let `A` be a ring with `Algebra ℚ A` and `Algebra L A`, and `S` a commutative
ring with `Algebra ℚ S` and `Algebra L S`.

- `scalarHom L A S` and `algebraHom L A S` are the ring homomorphisms from `L`
  to the center of `S ⊗[ℚ] A` given by `t ↦ algebraMap L S t ⊗ 1` and
  `t ↦ 1 ⊗ algebraMap L A t` (`scalarHom_val`, `algebraHom_val`;
  `tmul_central` shows that `1 ⊗ c` is central for central `c`).
- `tensorIdempotent L A S` is `idempotent (scalarHom L A S) (algebraHom L A S)`
  in `S ⊗[ℚ] A`. It is central (`tensorIdempotent_mul_comm`), idempotent
  (`tensorIdempotent_mul_self`), and
  `tensorIdempotent_mul_algebraMap` states
  `e * (1 ⊗ t) = e * (t ⊗ 1)` for `t : L`.
- `projection L A S : S ⊗[ℚ] A →ₐ[S] S ⊗[L] A` is the `S`-algebra map
  `s ⊗ a ↦ s ⊗ a` (`projection_tmul`); `projection_algebraHom` shows that it
  identifies the two actions of `L`, and `projection_tensorIdempotent` that it
  sends `e` to `1`.
- `liftAddHom L A S : S ⊗[L] A →+ S ⊗[ℚ] A` is the additive map
  `s ⊗ a ↦ e * (s ⊗ a)` (`liftAddHom_tmul`). It is well defined on the
  `L`-balanced tensor product because `e` makes the two actions of `L` agree.
  `liftAddHom_mul` shows it is multiplicative, `projection_liftAddHom` that
  `projection ∘ liftAddHom` is the identity, and `liftAddHom_projection` that
  `liftAddHom (projection x) = e * x`.

## The involution

Now let `σ : AlgebraInvolution ℚ A`.

- `IsConjugationOn L σ` is the proposition
  `∀ t : L, σ (algebraMap L A t) = algebraMap L A (conj t)`: `σ` acts on the
  image of `L` by complex conjugation (an involution of the second kind
  relative to `L`).
- `baseChange_tensorIdempotent`: under `IsConjugationOn L σ`, the
  scalar-extended involution `σ.baseChange S` (published in
  `Langlands.Shimura.Unitary.Involution`) sends `e` to `1 - e`. It fixes
  `scalarHom` and sends `algebraHom t` to `algebraHom (conj t)`, so this is
  `idempotent_conj`.
- `splitting σ S hσ : CentralExchangeSplitting (σ.baseChange S) (S ⊗[L] A)`
  has idempotent `e`, projection `projection L A S` and section
  `liftAddHom L A S`.
- `pointsEquiv σ S hσ : σ.Points S ≃* (S ⊗[L] A)ˣ × Sˣ` is
  `(splitting σ S hσ).similitudesEquiv`. Here `σ.Points S` is the published
  group `(σ.baseChange S).similitudes` of `Langlands.Shimura.Unitary.Adelic`.
  A point `(g, c)` goes to the unit `projection L A S g` and the multiplier
  `c` (`pointsEquiv_fst_val`, `pointsEquiv_snd`); the inverse sends `(a, c)`
  to `liftAddHom a + c • σ.baseChange S (liftAddHom a⁻¹)`
  (`pointsEquiv_symm_val`). All three hold by `rfl`.

## Naturality

Let `S'` be another commutative ring with `Algebra ℚ S'` and `Algebra L S'`,
and `f : S →ₐ[L] S'`.

- `projection_changeCoefficients`: `projection L A S'` composed with the
  published coefficient change `changeCoefficients` along `f` (viewed as a
  rational algebra map) equals `projection L A S` followed by
  `Algebra.TensorProduct.map f (AlgHom.id L A)`.
- `pointsEquiv_pointsMap`: `pointsEquiv` intertwines the published
  `σ.pointsMap f` with the map `(a, c) ↦ (f ⊗ id) a, f c` of units.

## Scope

The identification is purely algebraic: no topology is considered, and the
algebra `S ⊗[L] A` is not decomposed further. The forward map of
`pointsEquiv` involves only `projection L A S` and the multiplier, so it does
not depend on the choice of `generator L`; the idempotent and `liftAddHom` are
used only to construct the inverse. That the idempotent itself is independent
of the choice is not proved. The Library's `ImaginaryQuadraticProjectors` constructs
related idempotents in `R ⊗[ℚ] L` for algebras `R` over a field containing
`L`; here the idempotent is written directly in `S ⊗[ℚ] A` for every
commutative `L`-algebra `S`, with no field hypothesis.

## Provenance

Internal construction. It makes explicit, over an arbitrary commutative
`L`-algebra of coefficients, the computation behind Harris (1998), Appendix,
equation (A.1) on printed p. 206, and Harris (1999), equation (4.2) on printed
p. 309: when `p` splits in the imaginary quadratic field, the `p`-adic points
of the unitary similitude group are the units of one of the two factors of
`ℚ_p ⊗ B` times `ℚ_pˣ`. The explicit idempotent formula, the use of a generator
and the naturality statement are implementation choices.

Formal dependencies: `Langlands.Shimura.Unitary.CentralExchangeSplitting`,
`Langlands.Shimura.Unitary.Adelic` (with `Involution` and `Similitude`), and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
particular `IsCMField.complexConj`, `IsCMField.complexConj_ne_one`,
`Algebra.IsQuadraticExtension.finrank_eq_two`,
`LinearIndependent.span_eq_top_of_card_eq_finrank`,
`Algebra.TensorProduct.lift` and `TensorProduct.liftAddHom`.
