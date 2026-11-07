# Duality of induction from a compact quotient for every smooth representation

Author: Worker 937.

`Langlands.Induction.exists_integralDualEquiv_of_section` identifies the smooth
dual of the smooth induction of `twist χ (σ.comp m)` with the smooth induction
of `twist χ ((smoothContragredient σ).comp m)`. The identification is the
integral pairing over a measure on `K`, and it holds for every smooth `σ`. It
is a variant of `exists_integralDualEquiv_of_pos` (module
`CompactQuotientDuality`, Worker 805), which requires the induced
representation to be admissible (`hadm`). Here admissibility is replaced by
three structural hypotheses on `P`:

- `P` is closed in `G` (`hP`);
- the coset space `P \ G` is compact (`[CompactSpace (LeftQuotient P)]`);
- `m : P →* M` has a continuous group-homomorphism section `s : M →* P`
  (`hs`, `hms : ∀ n, m (s n) = n`).

The hypothesis `hcofM` (compact open subgroups cofinal in `M`) of the
admissible version is also dropped. The scalar hypothesis `hscalar` and the
positivity hypothesis `hpos` are the same as in `exists_integralDualEquiv_of_pos`.

## Provenance

Internal. The module states no definition or proposition taken from a source.
The identity is the compact-quotient case of the Theorem of Renard,
*Représentations des groupes réductifs p-adiques* (2026 version), III.2.7
"Induction et dualité" (printed p. 78, PDF p. 84):
`Ind_H^G(W̃) ≃ ind_H^G(W ⊗ δ_{H\G})~` for a closed subgroup `H` and every
smooth `W`, with the duality given by an integral over `H \ G`. When `H \ G` is
compact, `ind = Ind`, and VI.1.2 uses this to make the normalized `i_P^G`
commute with contragredients. Renard deduces the theorem from the adjunctions
of III.2.6 and Theorem I.4.2. The Lean proof does not follow that route. It is
the fixed-vector computation over the finitely many double cosets `P \ G / L`
written out below. The definition `fixedSectionMap` is a codomain restriction
of the Library's `sectionMap`, made for this proof.

## Statement

Let `G` be a nonarchimedean topological group, weakly locally compact, `P` a
subgroup, `m : P →* M` a continuous homomorphism to a topological group `M`,
`χ : P →* ℂˣ` a character with open kernel, and `δ : P → ℝ≥0` with
`χ q * χ q = δ q` (`hδ`). Let `K` be a subgroup of `G` with a measure `μ`
positive on open neighbourhoods of `1` (`hpos`) whose integral is right
invariant on `δ`-covariant locally constant functions (`hscalar`). Under the
three hypotheses above, for every smooth complex representation `σ` of `M`
there is a representation equivalence `E` from the smooth contragredient of
`smoothInduced P (twist χ (σ.comp m))` to
`smoothInduced P (twist χ ((smoothContragredient σ).comp m))` such that, for
every smooth functional `ℓ` and every smooth induced function `f`,

`ℓ f = ∫ k : K, ⟨(E ℓ)(k), f(k)⟩ dμ`.

## Proof

The final step is `Langlands.exists_smoothDualEquiv_of_fixedSurjective`
(module `Smooth/Contragredient/FixedLevelPairing`). It applies to the
integral pairing `b = integralBilinearPairing` between the two inductions. The
invariance of `b` is `hscalar` applied to the covariant function
`y ↦ ⟨h(y), f(y)⟩`. Nondegeneracy in the dual variable is the published
`integral_dualPairing_left_nondegenerate_of_pos`. Compact open subgroups are
cofinal in `G` by `compactOpenSubgroupBasis`. What remains is surjectivity at
each compact open level `L`, which is `integralBilinearPairing_fixed_surjective`.
The equivalence `E` is the inverse of the equivalence given by
`exists_smoothDualEquiv_of_fixedSurjective`.

### Compactness of the stabilizers

For `x ∈ G` write `H_x = P ∩ x L x⁻¹`, as the open subgroup
`conjOpenSubgroup P L x` of `P`.

- The existing `isCompact_conjOpenSubgroup` from `Induction.SurjectivityProof`
  gives compactness of `H_x`. It is the preimage under the
  closed embedding `P → G` of the compact set `x L x⁻¹`.
- `character_mul_self_eq_one_of_isCompact`: `χ h * χ h = 1` for `h` in a
  compact subgroup `H`. The kernel of `χ` on `H` is open, so it has finite
  index `n` in `H`, and `χ(h)ⁿ = 1`. Hence `δ(h)ⁿ = 1` with `δ(h) ≥ 0`, so
  `δ(h) = 1`.

### Functionals on fixed coefficient spaces

`exists_fixed_smoothDual_of_section`: for a compact open subgroup `H` of `P`,
every linear functional `φ` on the `H`-fixed vectors of `twist χ (σ.comp m)`
is the pairing with some `λ` in the smooth dual of `σ` that is `H`-fixed in
`twist χ ((smoothContragredient σ).comp m)`. The representation
`twist χ (σ.comp m)` of `P` is smooth, so
`smoothDualFixedRestriction_bijective` gives an `H`-fixed smooth functional
`ℓ` of it restricting to `φ`. This `ℓ` is fixed by some open subgroup `U` of
`P`. Then `ℓ` is fixed under `σ.dual` by the open subgroup
`s⁻¹(U ∩ ker χ)` of `M`, because `m ∘ s = id`. So `ℓ` is a smooth functional
`λ` of `σ`. This is the only use of the section `s`. That `λ` is `H`-fixed for
the twisted contragredient uses `χ(h⁻¹) = χ(h)` on the compact `H`, from the
previous lemma.

### The pairing with a double-coset section

For `λ` fixed by `H_x`, the Library's `compactDoubleCosetSection` at `x`
through `λ` is the function supported on `P x L` with value
`χ(a) σ̃(m a) λ` at `a x b`.

- `pairing_section_mul`: at `a x b` its pointwise pairing with an `L`-fixed
  `f` is `χ(a)² ⟨λ, f(x)⟩`, by `dualPairing_covariant`.
- `pairing_section_of_ne`: off the double coset `P x L` the pointwise pairing
  vanishes, by `section_eval_of_ne`.
- `exists_integral_section_eq`: there is `c ≠ 0`, depending only on `x` and
  `L`, with `∫_K ⟨section(k), f(k)⟩ dμ = c ⟨λ, f(x)⟩` for all such `λ` and all
  `L`-fixed `f`. If every `H_x`-fixed vector of `twist χ (σ.comp m)` is zero,
  then `f(x) = 0` and both sides vanish, so `c = 1` works. Otherwise pick a
  nonzero `H_x`-fixed `v₁`, a functional nonzero on it, and by the previous
  section a fixed `λ₁` with `⟨λ₁, v₁⟩ ≠ 0`. Let `ψ₁` be the pointwise pairing
  of the section through `λ₁` with the section `f₁` through `v₁`
  (`fixedDoubleCosetSection`). The two lemmas above give the pointwise identity
  `⟨λ₁, v₁⟩ ⟨section_λ(y), f(y)⟩ = ⟨λ, f(x)⟩ ψ₁(y)` for every `y`. Integrate it.
  The published `integral_ne_zero_of_doubleCoset_of_pos` shows
  `∫_K ψ₁(k x) dμ ≠ 0`, and `hscalar` moves the integral to `∫_K ψ₁(k) dμ`.
  Take `c = ∫_K ψ₁ dμ / ⟨λ₁, v₁⟩`.

### Surjectivity at a compact open level

`P \ G / L` is finite (`finite_doubleCosetQuotient`, which uses compactness of
`P \ G`). `dual_apply_eq_sum_fixedDoubleCosetSection` writes a functional `φ`
on the `L`-fixed induced vectors as
`φ f = ∑_q φ(section_q (f(x_q)))`, with `x_q` the chosen representative of
`q`. It follows from the Library's decomposition `subtype_eq_sum`. The
auxiliary `fixedSectionMap` is the section at `x` as a linear map into the
`L`-fixed vectors.

`integralBilinearPairing_fixed_surjective`: for each `q`, take the constant
`c_q` of `exists_integral_section_eq` at `x_q`, and take `λ_q` from
`exists_fixed_smoothDual_of_section` for the functional
`c_q⁻¹ (φ ∘ section_q)` on the `H_{x_q}`-fixed vectors. The sum of the sections
through the `λ_q` is `L`-fixed. Its integral pairing with `f` is
`∑_q c_q ⟨λ_q, f(x_q)⟩ = ∑_q φ(section_q (f(x_q))) = φ f`.

## Scope

The module proves no proposition of the Library's statement layer. It removes
admissibility from the induction-contragredient identity used in the second
adjointness theorem of Renard VI.9.6. Applying it to a parabolic `P` of a
reductive group needs compactness of `P \ G`, a Levi section and the scalar
hypothesis for the modulus. Those are separate inputs, not proved here.
