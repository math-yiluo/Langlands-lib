# Retractions onto representations with compact coefficients

This derived module constructs the intertwiner used to prove the injectivity half of
the unchanged `CompactCoefficientInjectiveProjectiveStatement`. All declarations are in
`Langlands.Cohomology.SupercuspidalExtCharZero`.

## Provenance

Vignéras (1996), Proposition I.7.10, printed page 62, obtains injectivity over an
algebraically closed field from projectivity of the contragredient `Ṽ` and the
admissibility identity `V = (Ṽ)~`. This module avoids the contragredient as a
projective object. It builds an explicit intertwiner back from any representation that
contains `ρ`. The pairing below is the coefficient construction of
`Langlands.Cohomology.SupercuspidalExtCharZero.CoefficientMap`, written in a dual form.
Admissibility enters only through the finite-dimensional bidual argument
`exists_eq_eval_of_invariant`. This route is derived for this project.

Throughout, `k` is a field of characteristic zero, `G` a topological group, `ρ` a
representation on `V` and `τ` a representation on `Y`. `SmoothDual ρ` is the Library's
space of smooth functionals, with the action `smoothContragredient ρ`
(`Langlands.Representation.Smooth.Contragredient.Definitions`). Averaging is Worker
1643's `Langlands.Compact.CharZero.averageMap`.

## The bidual lemma

- `smoothContragredient_apply_val`: the functional underlying
  `smoothContragredient ρ g ψ` is `ρ.dual g ψ.val`. This holds by definition and needs no
  `CharZero` hypothesis.
- `exists_eq_eval_of_invariant ρ hρ K hK Φ hΦ`: let `ρ` be smooth, `K` a compact open
  subgroup with `fixedVectors ρ K` finite-dimensional, and `Φ` a linear form on
  `SmoothDual ρ` invariant under `smoothContragredient ρ g` for `g ∈ K`. Then there is a
  `K`-fixed vector `v` with `Φ ψ = ψ.val v` for every smooth functional `ψ`.

  Proof. Extending functionals on `F = fixedVectors ρ K` along `fixedProjection` gives
  a linear map `ext` from `Module.Dual k F` to `SmoothDual ρ`
  (`fixedExtension_isSmoothVector`). Since `F` is finite-dimensional,
  `Φ ∘ ext` is evaluation at some `v ∈ F` (`Module.evalEquiv`). For a smooth `ψ`, let
  `ψ'` be its `K`-average in the smooth contragredient. The contragredient is smooth by
  the Library's `isSmooth_smoothContragredient`. `apply_averageMap_of_invariant` then
  gives three identities. First, `Φ ψ' = Φ ψ`. Second, `ψ'.val v = ψ.val v`, because
  evaluation at the `K`-fixed `v` is `K`-invariant. Third, `ψ'` is `K`-invariant, so
  `ψ'.val` is unchanged by the projection onto `F`, and `ψ' = ext (ψ'.val|F)`. Together
  these give `Φ ψ = (Φ ∘ ext)(ψ'.val|F) = ψ'.val v = ψ.val v`.
- `eq_of_forall_smoothDual`: for a smooth `ρ` of a Hausdorff, locally compact, totally
  disconnected `G`, two vectors on which all smooth functionals agree are equal. This
  follows from `eq_zero_of_forall_smooth_dual`.

## The pairing

`retractionPairing ρ τ U η w y ψ = cosetSum U (fun g => η (τ g⁻¹ y) * ψ (ρ g w))` for a
subgroup `U`, `η : Module.Dual k Y`, `w : V`, `y : Y` and `ψ : Module.Dual k V`. The
following facts assume only the hypotheses their statements list. In them `U` is open,
`η` is `U`-invariant and `w` is `U`-fixed.

- `retractionPairing_hasFiniteSupport`: if `g ↦ ψ (ρ g w)` has compact support, the
  summand has finite support on `G ⧸ U`.
- `retractionPairing_add_left` and `retractionPairing_smul_left`: linearity in `y`.
- `retractionPairing_rightInvariant`: the summand is right `U`-invariant.
- `retractionPairing_apply_rep`: the pairing at `τ h y` and `ψ` equals the pairing at
  `y` and `ψ ∘ ρ h`. The proof uses `cosetSum_mul_left`.
- `retractionForm hU hc y` is the pairing at `y` as a linear form on `SmoothDual ρ`.
  `hc` states that `g ↦ ψ (ρ g w)` has compact support for smooth `ψ`.
  `retractionForm_apply` is its application law.
- `retractionForm_invariant`: if `y` is fixed by a subgroup `K`, this form is
  invariant under `smoothContragredient ρ g` for `g ∈ K`.
- `retractionPairing_apply_intertwining`: if `i : ρ → τ` is an intertwiner with
  `η (i v) = ξ v` for all `v`, and the coefficients of `ξ` have compact support, then
  the pairing at `i v` and `ψ` is `ψ (coefficientMap ρ ρ U ξ w v)`.

## The retraction

`exists_intertwining_comp_eq_coefficientMap` assumes that `G` is Hausdorff, locally
compact and totally disconnected and that `ρ` is smooth. It also assumes `hadm`,
finite-dimensional fixed vectors under every compact open subgroup, and `hc`, compactly
supported coefficients against smooth functionals. Let `τ` be smooth, `i : ρ → τ` an
injective intertwiner, `U` a compact open subgroup, `ξ` a `U`-invariant functional and
`w` a `U`-fixed vector. The conclusion is an intertwiner `r : τ → ρ` with
`r (i v) = coefficientMap ρ ρ U ξ w v` for all `v`.

1. Choose a linear left inverse `r₀` of `i`. Put `η = ξ ∘ r₀ ∘ averageMap τ U`. It is
   `U`-invariant (`averageMap_apply_rho`). It satisfies `η ∘ i = ξ`, because averaging
   commutes with `i` (`averageMap_commute`) and `ξ` is `U`-invariant.
2. For each `y`, choose a compact open `K` fixing `y` (`exists_compact_fixing`). The form
   `retractionForm y` is `K`-invariant, and `fixedVectors ρ K` is finite-dimensional by
   `hadm`. By the bidual lemma it is the evaluation at some `r y ∈ V`. The vector is
   chosen with `choose`.
3. Smooth functionals separate vectors (`eq_of_forall_smoothDual`). Additivity,
   homogeneity and equivariance of `r` therefore follow from the corresponding
   properties of the pairing. Equivariance uses `retractionPairing_apply_rep` with the
   functional `ρ.dual h⁻¹ ψ`.
4. The identity `r (i v) = coefficientMap ρ ρ U ξ w v` follows in the same way from
   `retractionPairing_apply_intertwining`.
