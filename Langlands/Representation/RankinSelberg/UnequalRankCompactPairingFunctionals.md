# Unequal-rank compact pairings and inverse-standard Whittaker functionals

Author: Worker 896. Uses the published construction
`Induction.CompactFunctionalPairing.exists_nonzero_form` of Worker 605 and Worker 805.

Module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals`.
This is a helper step towards the proof of
`Langlands.RankinSelberg.UnequalRankCompactGenericPairingStatement`. It states no
new proposition and does not prove that statement. Its last theorem is that
statement's conclusion under one extra hypothesis: the inverse-standard
Whittaker functionals of `η` form a line. That is Whittaker multiplicity one,
which the Library still has only as the unproved
`Langlands.Whittaker.MultiplicityOneStatement`.

Notation: `N = GeneralLinear.upperUnipotent (n + 1) F`,
`θ = standardCharacter ψ n`, `θ' = inverseStandardCharacter ψ n`.
`forms(r, s)` is the published space
`unequalRankMirabolicForms hnr ψ abv (mirabolicCompactInduced ψ r) η s` for
`n < r`, and `Wh(η)` is `Whittaker.functionals N θ' η`.

## Main results

In section `Generic`, `F` is a field with
`[TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]`, and every
`GL_m F` is a locally compact nonarchimedean group. The section also fixes a
Borel measure `ν` on `N \ GL_(n+1)`. The common hypotheses are:

- `hψ`: the kernel of `ψ` is open.
- `hopen : Shahidi.IsOpenNormOne abv`.
- `hker`: the kernel of `θ` is open.
- `hinv`: `ν` is invariant under every right translation.
- `hmass`: every compact open subgroup orbit has positive finite `ν`-mass.
- `hη : IsSmooth η`.

The `exists_ne_zero*` theorems and `nonempty_equiv_complex` also assume
`[IsFiniteMeasureOnCompacts ν]`.

The theorems are:

- `exists_injective_adjacent`, `exists_injective`: for every `n < r` and
  every `s` there is an injective linear map `forms(r, s) →ₗ[ℂ] Wh(η)`.
- `exists_ne_zero_adjacent`, `exists_ne_zero`: if moreover
  `Whittaker.HasFunctional (N := N) (θ := θ') η`, then `forms(r, s)` has a
  nonzero element.
- `nonempty_equiv_complex`: if in addition
  `hline : ∀ ℓ₁ ℓ₂ : Wh(η), ℓ₁.val ≠ 0 → ∃ c, ℓ₂ = c • ℓ₁`, then
  `Nonempty (forms(r, s) ≃ₗ[ℂ] ℂ)`.

The p-adic specialization is:

```lean
theorem nonempty_equiv_complex_padic {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n r : ℕ) :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W,
      IsSmooth η →
      Whittaker.HasFunctional
        (N := GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (θ := Whittaker.inverseStandardCharacter ψ n) η →
      (∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁) →
      ∀ s : ℂ,
        Nonempty
          ((unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
            (Whittaker.mirabolicCompactInduced ψ r) η s) ≃ₗ[ℂ] ℂ)
```

Compared with the target statement, it has two differences:

- it asks only `IsSmooth η`, which is implied by `IsAdmissible η`, and no
  irreducibility;
- it adds the line hypothesis on `Wh(η)`.

Its other parameters and binders are the target's: the supplied topology, the
normalized absolute value, the actual compact model and the independent
universes `uF` and `uW`.

## Proofs

1. **Adjacent rank, upper bound (`exists_injective_adjacent`).** Compose the
   equivalence `formsAdjacentEquiv` of `UnequalRankCompactPairingBase` with the
   published injection `Induction.FormsFunctional.exists_injective_formsFunctional`
   for `c-Ind_N^(GL_(n+1)) θ × η`. That injection takes as inputs:
   - `θ'`, with `θ' θ = 1` (`inverseStandardCharacter_mul`);
   - closedness of `N` (`GeneralLinear.UpperUnipotent.isClosed`);
   - smoothness of the character from `hker`;
   - a compact open subgroup basis (`compactOpenSubgroupBasis`).
2. **Adjacent rank, existence (`exists_ne_zero_adjacent`).** Take a nonzero
   `ℓ ∈ Wh(η)`. The published `CompactFunctionalPairing.exists_nonzero_form`
   gives a nonzero invariant form on `c-Ind_N^(GL_(n+1)) θ × η`. Transport it
   back along `formsAdjacentEquiv`.
3. **All ranks (`exists_injective`, `exists_ne_zero`).** Induction on
   `r ≥ n + 1` (`Nat.le_induction` with an explicit motive quantified over `s`).
   The step uses the published equivalence
   `formsSuccEquiv : forms(m, s - 1/2) ≃ₗ forms(m + 1, s)` of
   `UnequalRankCompactPairingReduction`.
4. **Line (`nonempty_equiv_complex`).**
   - `exists_injective_of_forall_eq_smul` turns `hline` into an injective linear
     map `Wh(η) → ℂ`: every functional is a multiple of a fixed nonzero one, via
     `LinearEquiv.toSpanNonzeroSingleton`.
   - Composing with step 3 gives an injective linear map `forms(r, s) → ℂ`.
   - Together with the nonzero form of step 3, the published
     `MirabolicCompactTwistedPairing.nonempty_linearEquiv_complex` gives
     `forms(r, s) ≃ₗ[ℂ] ℂ`.
5. **p-adic specialization.** The instances come from `T`, as in the published
   `MirabolicCompactTwistedPairingProof`:
   - `T.fieldT2`;
   - `T.generalLinearNonarchimedean`, `T.generalLinearLocallyCompactSpace`;
   - that module's public `MirabolicCompactTwistedPairing.valuative_nonarchimedean`,
     for the nonarchimedean additive structure. Integration exposed the existing
     helper with its statement and proof unchanged and removed the duplicate copy.

   The hypotheses are discharged as follows:
   - `hψ`: `MirabolicWhittaker.isOpen_complex_eq_one`;
   - `hopen`: `MirabolicCompactTwistedPairing.isOpenNormOne_normalizedAbsoluteValue`;
   - `hker`: `isOpen_ker_of_continuous_complex_character`;
   - `ν`: the published `RankinSelberg.unipotentQuotientHaar F n` with Borel
     structures. `hinv` and `hmass` come from its compatibility
     `unipotentQuotientHaar_isCompatible` (`right_invariant`,
     `compactOpenQuotientOrbit_mass`).

## Provenance

The forms are those of JPSS (1983), Section 2.11, (2.11.2) and (2.11.4). The
statement whose conclusion `nonempty_equiv_complex_padic` gives conditionally is
the compact/generic case of the Lemma on p.399, discussed on p.403
(literature ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). In the
source, the line conclusion rests on uniqueness of Whittaker functionals, recalled
in Section 2.1. Here that input appears as the explicit hypothesis `hline`.

The route is internal and derived:

- reduction in rank by restriction;
- the adjacent-rank identification of `UnequalRankCompactPairingBase`;
- the published compact-induction upper bound and the published nonzero pairing.

`exists_injective_of_forall_eq_smul`, `inverseStandardCharacter_mul` and the
imported `MirabolicCompactTwistedPairing.valuative_nonarchimedean` are elementary
helpers.
