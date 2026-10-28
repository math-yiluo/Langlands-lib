# Proof: the compact mirabolic twisted pairing is one-dimensional

Author: Worker 805.

```lean
theorem Langlands.Whittaker.mirabolicCompactTwistedPairing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    MirabolicCompactTwistedPairingStatement.{uF} F T n
```

proves the unchanged Library proposition
`Langlands.Whittaker.MirabolicCompactTwistedPairingStatement` from
`Langlands.Representation.Whittaker.MirabolicPairingStatement`: for every prime
`p`, p-adic field `F` with supplied topological data `T` (and the canonical
topology `T.topology`), every rank `n`, every unitary additive character `ψ` and
every `s : ℂ`,

```text
Nonempty (InvariantBilinear.forms (mirabolicCompactInduced ψ n)
  (mirabolicCompactInduced ψ n)
  (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)) ≃ₗ[ℂ] ℂ),
```

that is, `dim Bil_P(τ ⊗ α^s, τ) = 1` for the actual compact model `τ` (BZ76's
`τ_P⁰`, JPSS's `τ_r`), as used on JPSS (1983) p.398. No hypothesis is added; the
nontriviality of `ψ` is part of the published structure `UnitaryAdditiveCharacter`.

## Route

Write `τ_ψ = mirabolicCompactInduced ψ n`, `N = Mirabolic.upperUnipotent n F`,
`θ_ψ = mirabolicCharacter ψ n`, and `ψ⁻ = ψ.scale (-1)`, so that
`ψ⁻(x) = ψ(-x)` and `θ_ψ⁻ = θ_ψ⁻¹` (`mirabolicCharacter_scale_neg_one_mul`, from
the published product formula `mirabolicCharacter_eq_product`).

1. **Removing the twist.** The published adapter
   `mirabolicFormsDeterminantShift` (module `MirabolicCompactAdapters`) with
   `c = -s`, `κ = |det|^(-s)` and `κ' = 1` identifies
   `forms(τ_ψ, τ_ψ, |det|^(-s))` with `forms(τ_ψ, τ_ψ, 1)`. It needs
   `Shahidi.IsOpenNormOne (normalizedAbsoluteValue T)`, which
   `isOpenNormOne_normalizedAbsoluteValue` derives from the published
   `T.isOpen_ker_normalizedAbsUnits`: both kernels are the units with
   `T.normalizedAbs a = 1`.
2. **Opposite character.** The published equivalence
   `mirabolicCharacterChangeEquiv ψ (-1) n : τ_ψ ≅ τ_ψ⁻` (left translation by the
   diagonal element `diag((-1)^n, …, -1, 1)`, BZ76 §5.6) is applied to the second
   argument with `InvariantBilinear.equivRight`. This gives
   `forms(τ_ψ, τ_ψ, 1) ≃ X := forms(τ_ψ, τ_ψ⁻, 1)`, the form of the space in the
   proof of JPSS §1.5, Corollary 1, p.384.
3. **`X` is a line** (`nonempty_oppositeForms_equiv`). Given a measure `ν` on
   `N \ P` that is finite on compacts, right invariant, and positive and finite on
   orbits of compact open subgroups:
   - `FormsFunctional.exists_injective_formsFunctional` (module
     `Induction.CompactFormsFunctional`) gives an injective linear map
     `L : X → Whittaker.functionals N θ_ψ⁻ τ_ψ⁻`, `B ↦ ℓ_B` with
     `ℓ_B(w) = ν(orbit K)⁻¹ B(s_K, w)`;
   - `MirabolicWhittaker.exists_testVector` (module
     `MirabolicCompactWhittakerUniqueness`, applied to `ψ⁻`) gives `f₀` such that
     `E : ℓ ↦ ℓ f₀` is injective on these functionals;
   - `FormsFunctional.exists_standardForm` gives a nonzero
     `B_std(f₁, f₂) = ∫_{N \ P} f₁ f₂ dν` in `X`;
   - `nonempty_linearEquiv_complex`: an injective functional `E ∘ L : X → ℂ` and a
     nonzero vector make `E ∘ L` bijective, since `E (L B_std) ≠ 0` and
     `(c / E(L B_std)) • B_std` maps to `c`.

   The general hypotheses are discharged as follows: compact open subgroups of
   `P` form a neighbourhood basis (`compactOpenSubgroupBasis`, with
   `MirabolicWhittaker.mirabolic_nonarchimedean` and
   `Mirabolic.locallyCompactSpace`); `N` is closed
   (`Mirabolic.upperUnipotent_isClosed`); the character representation of `θ_ψ`
   is smooth because `θ_ψ` has open kernel (`isSmooth_characterRepresentation`);
   compact induction is smooth (`compactInduced_smooth`); the kernel of `ψ⁻` is
   open (`MirabolicWhittaker.isOpen_complex_eq_one`).
4. **Instances for the p-adic field** (main theorem). With `T.topology`,
   `T.valuativeRel` and `T.localField`: `T.fieldT2`; the field is a
   nonarchimedean additive group (`valuative_nonarchimedean`, from the open
   submodule basis of the valuation integers; a copy of the private lemma in
   `HarmonicAnalysis.PadicRowFourierCutoffStatement`); `GL_m` is nonarchimedean
   and locally compact (`T.generalLinearNonarchimedean`,
   `T.generalLinearLocallyCompactSpace`). The kernel of `θ_ψ` is open as the
   preimage, under the published homeomorphism
   `Mirabolic.upperUnipotentContinuousEquiv`, of the kernel of the continuous
   standard character (`standardCharacterContinuous`,
   `isOpen_ker_of_continuous_complex_character`, with
   `T.upperUnipotentNonarchimedean`). The quotient `N \ P` receives its Borel
   structure, and `MirabolicQuotient.exists_measure` (module
   `MirabolicQuotientMeasure`) supplies `ν`: the Dirac measure in rank zero, and
   in positive rank the published `RankinSelberg.unipotentQuotientHaar`
   transported along the homeomorphism `N \ P ≅ N_GL \ GL_n`.

Composing 1, 2 and 3 gives the required equivalence with `ℂ`.

## Helper modules

The proof imports three helper modules shipped with it:

- `Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness`
  (also submitted separately as a lean.definition candidate): uniqueness of
  Whittaker functionals on the compact model, by induction on the rank via
  restriction along the successor embedding. It uses no minimality,
  scalar-Hom or functional-multiplicity result.
- `Langlands.Representation.Induction.CompactFormsFunctional`: invariant forms
  on a compactly induced character embed into equivariant functionals for the
  inverse character, and the standard pairing is a nonzero invariant form.
- `Langlands.Representation.Whittaker.MirabolicQuotientMeasure`: the measure on
  `N \ P`.

Each has its own Markdown with the detailed argument.

## Relation to the literature

JPSS (1983), §1.5, and the use on p.398 obtain this dimension from their
Proposition 1.4 and the identification of the opposite-character compact
induction with `τ_r`. The implemented proof instead reduces to `s`-independent
forms `forms(τ_ψ, τ_ψ⁻, 1)` with the two adapters, bounds their dimension by
Whittaker uniqueness on `τ_ψ⁻` (the dual form of the "at most one" half of
`dim E_{U,Θ} = 1` in the proof of BZ76 Proposition 5.15(b), p.50), and
exhibits the integral pairing for existence.
