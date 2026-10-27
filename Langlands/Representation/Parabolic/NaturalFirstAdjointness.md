# Natural normalized first adjointness

Author: Worker 733.

This module proves first adjointness (Frobenius reciprocity) for the
Library's normalized parabolic induction, in two settings. In the first, `GL_n`
is induced from a standard block Levi. In the second, the coarse product Levi
`B.Levi` is induced from a refined Levi. In both settings the identification is
natural in both variables. It is the form of Casselman, Chapter III
(`casselman-2019-jacquet-module`, revision April 29, 2019), Proposition III.3.5:
for a smooth `(π, V)` and a representation `σ` of the Levi, evaluation at `1`
gives

\[
 \operatorname{Hom}_G(\pi, \operatorname{Ind}(\sigma)) \cong
 \operatorname{Hom}_M(\pi_N, \sigma).
\]

The Lean source applies this in two directions. It uses the Library's
normalized induction (positive half-modulus covariance) and the Library's
normalized Jacquet module (inverse half-modulus action), and it proves the
naturality equations. The naturality equations are not stated in the source;
they are routine consequences of the definitions. No hypothesis on `σ` beyond
being a representation is needed. The source `X` must be smooth so that orbit
functions land in the smooth induced space.

## Standard parabolic of `GL_n`

Namespace `Langlands.Parabolic.FirstAdjointness`, section `Standard`.
Here `T : F.TopologicalData`, `B : BlockShape n`, `ρ` is a representation of
`GeneralLinear n F.Carrier` and `σ` is a representation of `B.Levi F.Carrier`.

- `jacquetMk_parabolic`: in the unnormalized Jacquet quotient, `ρ(q) v` and
  `ρ(m) v` have the same class, where `m` is the Levi part of `q` embedded in
  `GL_n`. The proof writes `q = u · m` with `u` the unipotent part,
  and uses `Jacquet.mk_apply_subgroup` for `u`.
- `jacquetMk_levi`: the class of `ρ(m) v` is `δ_P(m)^(1/2)` times the
  normalized Jacquet action of `m` on the class of `v`. It undoes the published
  `normalizedJacquet_mk_eq_inv_halfModulus`.
- `jacquet_covariant`: for an intertwiner
  `A : (T.normalizedJacquet B ρ) → σ`, the function `g ↦ A[ρ(g) v]` satisfies
  the positive half-modulus covariance of normalized induction. This combines
  the two lemmas above with the intertwining property of `A`.
- `orbitMap A` is the intertwiner from `ρ` to the full (not necessarily smooth)
  covariant function space, with `v ↦ (g ↦ A[ρ(g) v])`. Right translation
  matches the action of `ρ`.
- `frobenius T B hρ A` restricts `orbitMap A` to the smooth induced space by the
  Library's `smoothLift`, using smoothness `hρ` of the source. The simp lemma
  `frobenius_eval` records that the value at `g` is `A[ρ(g) v]` (by `rfl`).
- `equiv T B hρ` is the linear equivalence
  `Hom(ρ, i_P σ) ≃ₗ[ℂ] Hom(r_P ρ, σ)`. Its forward map is the published
  `CuspidalSupport.jacquetEvaluation` (evaluation at `1`, descended to the
  Jacquet module), and its inverse is `frobenius`. The left inverse property
  is the published `CuspidalSupport.inducedEvaluation_translate`:
  `f(ρ(g) v)(1) = f(v)(g)`. The right inverse property and linearity are checked
  on Jacquet classes by `Representation.Coinvariants.hom_ext`, where they hold
  definitionally (using `ρ(1) = id`). `equiv_apply_mk` records the value on a
  class.
- `equiv_inducedMap`: for `c : σ → τ`,
  `equiv (i_P(c) ∘ f) = c ∘ equiv f`, where `i_P(c)` is
  `T.normalizedParabolicInducedMap B c`.
- `equiv_comp`: for `h : ρ' → ρ`, `equiv (f ∘ h) = equiv f ∘ r_P(h)`, where
  `r_P(h)` is `T.normalizedJacquetMap B h`.

Both naturality equations hold definitionally on Jacquet classes, so each proof
is `Coinvariants.hom_ext` followed by `rfl`.

## Parabolic of a product Levi

Section `Refined`. Here `S : BlockRefinement B`, `ρ` is a representation of the
coarse Levi `B.Levi F.Carrier` and `σ` is a representation of the whole refined
Levi `refinedLevi F.Carrier B S`. There is no tensor factorization. The
construction repeats the standard one, using the Library's refined parabolic,
refined unipotent radical, refined Levi projection and section
(`Geometric.RefinementDefinitions`), refined normalized induction
`T.normalizedRefinedInduced` and refined normalized Jacquet module
`T.normalizedRefinedJacquet` (`Geometric.RefinementFunctors`).

- `refinedJacquetMk_parabolic`, `refinedJacquetMk_levi`,
  `refinedJacquet_covariant`, `refinedOrbitMap`, `refinedFrobenius` and
  `refinedFrobenius_eval` are the refined analogues of the standard lemmas.
  The Levi lemma uses `normalizedRefinedJacquet_mk` and
  `refinedLeviInverseHalfModulus_eq_inv`.
- The Library has no refined evaluation map, so this module defines one.
  `refinedInducedEvaluation T B S f : V →ₗ[ℂ] W` sends `v` to `f(v)(1)`.
  - `refinedInducedEvaluation_translate` gives `f(ρ(g) v)(1) = f(v)(g)`, by
    the intertwining property of `f` evaluated at `1`.
  - `refinedInducedEvaluation_parabolic` says a refined parabolic element acts
    through its refined Levi part, twisted by the positive half modulus. This
    is the covariance of the induced function `f v`.
  - `refinedInducedEvaluation_unipotent` says refined unipotent elements act
    trivially, since their Levi part is `1`.
  - `refinedInducedEvaluation_levi` says a refined Levi element `m` acts by
    `T.refinedLeviHalfModulus B S m • σ(m)`. This is the parabolic case at
    `refinedLeviSection m`.
- `refinedJacquetEvaluation T B S f` descends `refinedInducedEvaluation` to the
  refined unipotent coinvariants by `Jacquet.lift`. Equivariance for the
  normalized action reduces to classes. There the inverse half modulus of the
  normalized action cancels the half modulus from
  `refinedInducedEvaluation_levi`. `refinedJacquetEvaluation_mk` records the
  value on a class.
- `refinedEquiv T B S hρ` is the linear equivalence
  `Hom(ρ, i σ) ≃ₗ[ℂ] Hom(r ρ, σ)`, with forward map `refinedJacquetEvaluation`
  and inverse `refinedFrobenius`. The inverse laws are proved exactly as in the
  standard case. `refinedEquiv_apply_mk` records the value on a class.
- `refinedEquiv_inducedMap` (`T.normalizedRefinedInducedMap B S c`) and
  `refinedEquiv_comp` (`T.normalizedRefinedJacquetMap B S h`) are the two
  naturality equations. Both are checked on classes by `rfl`.

## Use

The module `Langlands.Representation.Parabolic.SecondAdjointnessAssembly`
composes these equivalences with admissible Hom duality, induction duality
and Jacquet duality to obtain second adjointness.
