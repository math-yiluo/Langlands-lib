# The pairing of a stable-lift duality and its asymptotic evaluation

`Langlands/Representation/Aubert/General/StableLiftDualityPairing.lean` connects the
abstract duality `Ψ : r_U(π~) ≅ (r_O π)~` of
`Langlands/Representation/Aubert/General/IwahoriJacquetStableLift.lean` with the
asymptotic evaluation theorem `exists_compact_forall_stableLiftPairing_translate_eq` of
`Langlands/Representation/Aubert/General/StableLiftAsymptotics.lean`. It serves the proof
of Renard 2026, VI.9.6, Proposition (printed p.202 / PDF p.208), formulas (VI.9.6.4) and
(VI.9.6.5). It proves nothing about parabolic subgroups, split components or cones, and it
does not prove `LeviJacquetOppositePairingStatement`.

## Setting

`G` is a locally compact nonarchimedean topological group. `U`, `M`, `O` are subgroups of
`G` with `U` and `O` closed and `M` normalizing both (`hMU`, `hMO`).
`normalizedJacquetFunctor U M hU hMU` is the published normalized Jacquet functor: on the
`U`-coinvariants, `m ∈ M` acts by `χ_U(m) · [π(m) v]`, with
`χ_U = HaarModulus.closedInverseHalfCharacter U hU M hMU`; similarly `χ_O` for `O`.
`Ψ` is a natural isomorphism between `π ↦ r_U(π~)` and `π ↦ (r_O π)~`, as functors from
smooth representations of `G` to smooth representations of `M`.

## Definition

`stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ w`, for a smooth representation `A`, a
smooth functional `ℓ` of `A` and a vector `w` of `A`, is the value of `Ψ_A` at the class of
`ℓ` in `r_U(Ã)`, evaluated (by `smoothDualPairing`) on the class of `w` in `r_O(A)`:

`⟨Ψ_A [ℓ]_U, [w]_O⟩`.

It is exactly the left-hand side of the formula in `IsStableLiftDuality`. The definition is
internal to this development: Renard writes `⟨j_N(v), j_{N̄}(λ)⟩_P` for the corresponding
pairing (printed pp.203–204 / PDF pp.209–210) but gives no separate name to its
evaluation on representatives.

## Results

* `hasStableLifts_stableLiftDualityPairing`: if `Ψ` satisfies
  `IsStableLiftDuality U M O hU hO hMU hMO g Ψ`, then every vector `x` of every smooth `A`
  satisfies `HasStableLifts A.representation U M O g (stableLiftDualityPairing … Ψ A) x`.
  Apply the stable-lift formula to the class `[x]_O`: the `K`-fixed lift `v` it provides has
  `[v]_O = [x]_O`, so the pairing at `v` is the pairing at the class of `x`, which the
  formula identifies with `Λ(v)`.
* `stableLiftDualityPairing_translate`: if `χ_U(m) χ_O(m) = 1` for `m ∈ M`, then

  `⟨Ψ_A [π̃(m⁻¹) ℓ]_U, [w]_O⟩ = ⟨Ψ_A [ℓ]_U, [π(m) w]_O⟩`.

  The component `Ψ_A` is a morphism of representations of `M`. Applying it to the action of
  `m⁻¹` on `[ℓ]_U` gives `χ_U(m⁻¹) Ψ_A[π̃(m⁻¹)ℓ]_U`. On the other side the contragredient
  action of `m⁻¹`, paired with `[w]_O`, evaluates `Ψ_A [ℓ]_U` at the action of `m` on
  `[w]_O`, which is `χ_O(m) [π(m) w]_O`. Since `χ_U(m⁻¹) = χ_U(m)⁻¹ = χ_O(m)` is a nonzero
  scalar, it cancels. This is the computation of Renard, printed pp.204–205 / PDF
  pp.210–211, where the normalizations `δ_P^{1/2}(m)` and `δ_{P̄}^{1/2}(m)` cancel.
* `exists_compact_forall_stableLiftDualityPairing_translate_eq`: assume
  `HasOppositeIwahoriContractionBasis U M O g`, `IsStableLiftDuality … g Ψ`, and
  `χ_U(m) χ_O(m) = 1` for every `m ∈ M`. Then for every smooth `A`, vector `x` and smooth
  functional `ℓ` there is a compact set `C ⊆ O` such that every `t ∈ M` commuting with all
  of `M` and satisfying `π̃(t c t⁻¹) ℓ = ℓ` for all `c ∈ C` has

  `⟨Ψ_A [ℓ]_U, [π(t) x]_O⟩ = ℓ(π(t) x)`.

  This is `exists_compact_forall_stableLiftPairing_translate_eq` for the pairing above.
  Its two factorization hypotheses hold because the pairing is defined on classes. The
  stable-lift hypothesis is the first result. The translation law is the second result for
  `m = t`. Normalization of `O` by `t` comes from `t ∈ M` and `hMO`.
* `exists_pullback_iso_smoothDualPairing_eq`: let `M₁ = M₂` be two names for the same
  subgroup, and let `e₁ : H ≃ₜ* M₁` and `e₂ : H ≃ₜ* M₂` be identifications with equal values
  in `G`. A duality `Ψ` over `M₂` then gives, for every smooth `A`, an isomorphism

  `E : e₁^*(r_U(Ã)) ≅ (e₂^*(r_O A))~`

  of smooth representations of `H` such that `E [ℓ]_U` evaluated on `[w]_O` equals
  `⟨Ψ_A [ℓ]_U, [w]_O⟩`. After identifying `M₁` with `M₂` and `e₁` with `e₂`, `E` is the
  component at `A` of the published `contragredientCompPullbackIso` built from `Ψ`. That
  isomorphism keeps every functional, so the pairing identity holds by definition. This is
  the explicit form of `nonempty_contragredient_normalizedJacquet_pullback_iso` in
  `Langlands/Representation/Aubert/General/ContragredientJacquetTransport.lean`.

## Provenance

Derived. Renard proves (VI.9.6.4) and (VI.9.6.5) with the decomposition
`V^K = V^K_0 ⊕ V^K_*` and the sections `s^K_P` (printed p.205 / PDF p.211). This module
uses instead the stable-lift property of the published duality and the derived argument of
`StableLiftAsymptotics`. The translation law is Renard's `M`-equivariance computation
(printed pp.204–205 / PDF pp.210–211), and the pullback lemma is the published transport
along Levi identifications. The definition and the four results are supporting steps, not
statements taken from the source.
