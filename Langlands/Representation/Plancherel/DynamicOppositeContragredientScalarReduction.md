# Reduction of `j(π̌) = j(π)` to the duality adjunction

Worker 5. The module
`Langlands.Representation.Plancherel.DynamicOppositeContragredientScalarReduction`
proves that the target `ConditionalDynamicOppositeDualAdjunctionStatement`
(the bilinear adjunction IV.1 (11) with the smooth contragredient, for the
Library's actual opposite standard integrals on their convergence domains)
implies the target `ConditionalDynamicOppositeContragredientScalarStatement`
(Waldspurger's IV.3 (2) `j(π̌) = j(π)` for the canonical scalar
`conditionalCanonicalRationalScalar`). Both targets are stated in the module
`DynamicOppositeContragredientScalar`. Neither target is proved here.

Everything in this module is proved: one definition (the bilinear form
`compactPictureDualBilin`) and theorems. There are no new hypotheses beyond
those of the two targets.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- IV.1 (11), printed p.283 / PDF p.49:
  `⟨J_{P'|P}(π) f, f̌'⟩ = ⟨f, J_{P|P'}(π̌) f̌'⟩` for the rational
  continuations of the intertwining integrals, where `⟨ , ⟩` is the duality
  between `I_P^G V` and `I_P^G V̌`.
- IV.3, printed p.285–286 / PDF p.51–52: `j_P` is the rational function on
  `O_ℂ` with `J_{P|P̄}(π') J_{P̄|P}(π') = j_P(π')` on irreducible inductions;
  then "`j(π) = j(π̌)`. (2) Cela résulte de IV.1 (11)."

This module implements that one-line deduction. With the Library
parametrization `π = A ⊗ z`, one has `π̌ = Ǎ ⊗ z⁻¹`, so IV.3 (2) reads
`j_P(Ǎ ⊗ z⁻¹) = j_P(A ⊗ z)`. This is the form of the scalar target.

## The pairing is bilinear

`compactPictureDualPairing h K hK A φ φ'` (module
`DynamicOppositeContragredientScalar`) is
`∫_K φ̌(k)(φ(k)) dk` for a compact-picture section `φ` for `A` and a section
`φ'` for `A.contragredient`, against the Library's Haar probability
`CompactInduction.measure K hK`.

- `compactPictureDualPairing_integrable`: the integrand is locally constant on
  the compact group `K` (`Induction.bilinearPairing_isLocallyConstant`),
  hence integrable.
- `compactPictureDualBilin h K hK A`: the same pairing as a bilinear form
  `CompactInductionPicture h K A →ₗ[ℂ] CompactInductionPicture h K A.contragredient →ₗ[ℂ] ℂ`.
  Linearity in each argument is linearity of the integral.
  `compactPictureDualBilin_apply` records that it evaluates to the pairing.

## The pairing is nondegenerate (in the needed form)

`exists_compactPictureDualPairing_ne_zero`: for a semidirect decomposition
`P = M ⋉ U` of a closed `P` with closed `U` and continuous Levi projection, a
compact open `K` with `G = P K`, and a smooth representation `A` of `M`, if
some `a ∈ A` is nonzero then there are sections `φ` for `A` and `φ'` for
`Ǎ` with `compactPictureDualPairing h K hK A φ φ' ≠ 0`.

Proof as implemented.

1. Smooth functionals separate the vectors of `A`
   (`Induction.exists_smoothDual_ne_zero`, with compact open subgroups
   cofinal in the closed Levi), so some smooth `λ` has `λ(a) ≠ 0`.
2. `a` and `λ` are fixed by open subgroups of `M`, hence by open subgroups of
   `P` for the normalized inducing actions
   (`Induction.exists_twist_comp_fixed`). There is a compact open `L ≤ K`
   such that `P ∩ L` fixes both (`Induction.exists_compact_conj_fixed`,
   applied twice with `x₀ = 1`).
3. `Induction.compactDoubleCosetSection` gives normalized induced functions
   `f` for `A` and `f'` for `Ǎ`. They take the values `a` and `λ` on `L` and
   vanish off `P L`. Their restrictions to `K`
   (`normalizedInductionCompactEquiv`) are `φ` and `φ'`; the restriction does
   not change values on `K`.
4. `ψ(y) = f'(y)(f(y))` is covariant under `P` by the positive modulus
   `closedRestrictCharacter` (`Induction.dualPairing_covariant`,
   `closedHalfCharacter_mul_self`). It equals `λ(a)` on `L` and vanishes off
   `P L`, so `Induction.integral_ne_zero_of_doubleCoset` gives
   `∫_K ψ(k · 1) dk ≠ 0`. This integral is `⟨φ, φ'⟩`.

The double coset is based at `1`. So the proof uses no right translation of
the integral over `K`, no unimodularity of `G` and no relation between the
modulus and the modular character.

## Duality persists under rational continuation

The setting is that of the Library's `RationalOperatorContinuationData`
(module `RationalUnramifiedOperatorContinuation`) over the unramified
characters of a connected reductive `L`: a continuation `p` of a family
`A : Ω → V →ₗ W` consists of a regular denominator and a polynomial numerator.
Its continued operator is defined where the denominator is nonzero
(`p.regularRegion`).

- `continuedOperator_dualAdjoint`: let `sV : V →ₗ V' →ₗ ℂ` and
  `sW : W →ₗ W' →ₗ ℂ` be bilinear, `p` continue `A : Ω → V →ₗ W` and `q`
  continue `B : Λ → W' →ₗ V'`. Suppose that
  `sW (A w v) w' = sV v (B w⁻¹ w')` for all `w` in a nonempty open `D ⊆ Ω`
  with `w⁻¹ ∈ Λ`. Then
  `sW (p.continuedOperator z v) w' = sV v (q.continuedOperator z⁻¹ w')` at
  every `z ∈ p.regularRegion` with `z⁻¹ ∈ q.regularRegion`. Proof: with
  `a1(z) = sW (p.numerator z v) w'` and `a2(y) = sV v (q.numerator y w')`
  (regular by `isPolynomialOn_scalar_iff`), the regular function
  `σ(q.denominator) a1 − p.denominator σ(a2)` vanishes on `D`, hence is zero
  (`rationalUnramifiedRegular_eq_zero_of_isOpen`). Here `σ` is the
  inversion `b(z) ↦ b(z⁻¹)` (`unramifiedRegularInversion`). Evaluating at `z`
  and dividing by the two denominators gives the claim. This is the bilinear
  analogue of the Library's `continuedOperator_adjoint` (module
  `DynamicOppositeUnitaryNonnegativity`).
- `unramifiedRegularInversion_ne_zero`: `σ` preserves nonzero regular
  functions.
- `mul_unramifiedRegularInversion_eq_of_values`: for regular `a, b, a', b'`
  and a nonzero regular `N`, if `a'(w) b(w⁻¹) = a(w⁻¹) b'(w)` wherever
  `N(w) ≠ 0`, then `a' σ(b) = σ(a) b'`. Proof: `(a' σ(b) − σ(a) b') N`
  vanishes at every point, and the regular functions form a domain
  (`rationalUnramifiedRegularFunctions_isDomain`).
- `eq_rationalUnramifiedFunctionFieldInversion_of_mul_eq`: if `f = a/b`,
  `f' = a'/b'` with `b, b' ≠ 0` and `a' σ(b) = σ(a) b'`, then
  `f' = rationalUnramifiedFunctionFieldInversion f`.
- `continuedCompositeScalar_dual`: let `p, q` continue a forward family
  `A : V → W` and a reverse family `B : W → V`, and let `p', q'` continue a
  forward family `A' : V' → W'` and a reverse family `B' : W' → V'`. Assume
  the two adjunctions `sW (A w v) w' = sV v (B' w⁻¹ w')` on a nonempty open
  `D` and `sV (B w u) v' = sW u (A' w⁻¹ v')` on a nonempty open `E`. For
  `ℓ = c · sV(·, v')` and `ℓ' = c · sV(v, ·)`, the coefficient
  `ℓ(q(z) p(z) v)` equals `ℓ'(q'(z⁻¹) p'(z⁻¹) v')` whenever
  `z ∈ p.regularRegion ∩ q.regularRegion` and
  `z⁻¹ ∈ p'.regularRegion ∩ q'.regularRegion`. Proof: apply
  `continuedOperator_dualAdjoint` to `q, p'` and then to `p, q'`:
  `sV (q p v) v' = sW (p v) (p' v') = sV v (q' p' v')`.
- `continuedCompositeRationalScalar_dual`: in the same situation, with the four
  original regions nonempty, the fraction
  `continuedCompositeRationalScalar p' q' v' ℓ'` is
  `rationalUnramifiedFunctionFieldInversion` of
  `continuedCompositeRationalScalar p q v ℓ`. Proof: take regular
  presentations `a1/b1` and `a2/b2` from
  `continuedCompositeRationalScalar_spec`. Let
  `N = σ(p.den) σ(q.den) p'.den q'.den`. Where `N(w) ≠ 0`, the point `w⁻¹`
  lies in the regular regions of `p` and `q` and `w` lies in those of `p'`
  and `q'`, so `continuedCompositeScalar_dual` at `w⁻¹` gives
  `a1(w⁻¹)/b1(w⁻¹) = a2(w)/b2(w)`. Then apply the two
  previous lemmas.

## The reduction

`conditionalDynamicOppositeContragredientScalar_of_dualAdjunction`:

`ConditionalDynamicOppositeDualAdjunctionStatement →
  ConditionalDynamicOppositeContragredientScalarStatement`.

Proof as implemented. Fix the data of the scalar target: the continuations
`p, q` (forward and reverse integrals for `A`) and `p', q'` (for `Ǎ`), the
open sets, and the hypotheses `_hinvForward`, `_hinvReverse` that inversion
maps `DForward` into the reverse convergence domain for `Ǎ` and `DReverse`
into the forward convergence domain for `Ǎ`.

1. `exists_normalized_compactCoefficient` gives a section `v` for `A` with a
   functional `ℓ0`, `ℓ0 v = 1`. So `v ≠ 0` (`ne_zero_of_coefficient_eq_one`)
   and some value `v(k)` is a nonzero vector of `A`
   (`Induction.exists_eval_ne_zero`).
2. `exists_compactPictureDualPairing_ne_zero` gives sections `φ` for `A` and
   `φ'` for `Ǎ` with `c₀ = ⟨φ, φ'⟩ ≠ 0`.
3. Put `ℓ = c₀⁻¹ ⟨·, φ'⟩` and `ℓ' = c₀⁻¹ ⟨φ, ·⟩`, so that `ℓ φ = 1` and
   `ℓ' φ' = 1`. By `conditionalCanonicalRationalScalar_eq_extraction`, the
   scalar for `A` is the fraction extracted from `q ∘ p` by `φ, ℓ`. The scalar
   for `Ǎ` is the fraction extracted from `q' ∘ p'` by `φ', ℓ'`.
4. The first part of the adjunction target, on `DForward`, is the adjunction
   `D` of `continuedCompositeRationalScalar_dual`, with `sV` the pairing for
   `P` and `sW` the pairing for `P̄`. The second part, on `DReverse`, is the
   adjunction `E`. That lemma gives the conclusion.

## Use

Together with a proof of `ConditionalDynamicOppositeDualAdjunctionStatement`,
this gives IV.3 (2) for the canonical scalar. The density corollary
`plancherelDensity_contragredient_of_contragredientScalar` (module
`DynamicOppositeContragredientScalar`) then gives the fourth item of
Lemma V.2.1, `μ(ω̌) = μ(ω)`.

## Not proved here

- The adjunction target `ConditionalDynamicOppositeDualAdjunctionStatement`.
- Hence the scalar target, except conditionally on the adjunction target.

## Axioms

`conditionalDynamicOppositeContragredientScalar_of_dualAdjunction` and all
other results depend only on `propext`, `Classical.choice` and `Quot.sound`.
