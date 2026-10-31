# Proof of the unequal-rank compact generic pairing statement

Author: Worker 896.

Module `Langlands.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof`.
It proves the Library proposition
`Langlands.RankinSelberg.UnequalRankCompactGenericPairingStatement.{uF,uW} F T n r`
(module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`)
for every prime `p`, p-adic field `F`, supplied topological data `T` and natural
numbers `n`, `r`. The statement itself is not changed.

```lean
theorem unequalRankCompactGenericPairing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r
```

The statement says the following. Take `n < r`, a unitary additive character `ψ`,
an admissible irreducible representation `η` of `GL_(n+1)` on a carrier in
universe `uW`, and a nonzero inverse-standard Whittaker functional of `η`. Then
for every complex `s`, the covariance space `unequalRankMirabolicForms` of the
actual compact mirabolic model `Whittaker.mirabolicCompactInduced ψ r` and `η`
is complex-linearly equivalent to `ℂ`.

## Proof

The theorem is
`UnequalRankCompactPairing.unequalRankCompactGenericPairing_of_multiplicityOne`
(module `UnequalRankCompactPairingMultiplicity`) applied to the Library proof
`Whittaker.multiplicityOne.{uF,uW}` of Whittaker multiplicity one. The carrier
universe of multiplicity one is the universe `uW` of `η`.

The proof chain is as follows. Each named declaration is in the Library or in
this submission. Below, `forms(m, s)` is the covariance space
`unequalRankMirabolicForms` of the compact mirabolic model of rank `m` and `η`
at the exponent `s`.

1. `UnequalRankCompactPairingReduction`, `formsSuccEquiv`: for `n < m` and every
   `s`, restriction along the successor embedding gives a linear equivalence
   `forms(m, s - 1/2) ≃ₗ[ℂ] forms(m + 1, s)`. Induction on `m` from `m = n + 1`
   (`Nat.le_induction`) transports facts from the adjacent rank, at shifted
   exponents, to every rank `r > n`.
2. `UnequalRankCompactPairingBase`, `formsAdjacentEquiv`: at the adjacent rank
   `r = n + 1`, `forms_adjacent_eq` rewrites `forms(n + 1, s)` as the invariant
   forms on the restriction of the compact model to `GL_(n+1)` with covariance
   `|det|^(1/2 - s)`. The Levi identification `leviEquiv` replaces that
   restriction by `glCompactInduced ψ n`, the compact induction from the upper
   unipotent group of `standardCharacter ψ n`. `Induction.formsCharacterShift`
   then absorbs the determinant weight into the compactly induced side. The
   result is a linear equivalence from `forms(n + 1, s)` to
   `InvariantBilinear.forms (glCompactInduced ψ n) η (fun _ => 1)`, with `η`
   itself untwisted.
3. `UnequalRankCompactPairingFunctionals` uses two separate facts about these
   invariant forms:
   - Injection (`exists_injective_adjacent`):
     `Induction.FormsFunctional.exists_injective_formsFunctional` (module
     `Induction.CompactFormsFunctional`) gives an injective linear map from the
     invariant forms to the inverse-standard Whittaker functionals of `η`.
   - Nonzero form (`exists_ne_zero_adjacent`):
     `Induction.CompactFunctionalPairing.exists_nonzero_form` (module
     `Induction.CompactFunctionalPairing`, Worker 605) builds a nonzero
     invariant form from the supplied nonzero inverse-standard functional.

   Composing with `formsAdjacentEquiv`, and then with the equivalences of step 1,
   gives both facts for every `r > n` and every `s` (`exists_injective`,
   `exists_ne_zero`).
4. `UnequalRankCompactPairingFunctionals`, `nonempty_equiv_complex`: suppose any
   two inverse-standard functionals are proportional to a nonzero one. Then
   `exists_injective_of_forall_eq_smul` injects the functional space into `ℂ`.
   Composed with the injection of step 3, this gives an injective linear map
   `forms(r, s) → ℂ`. The nonzero form of step 3 makes it bijective
   (`MirabolicCompactTwistedPairing.nonempty_linearEquiv_complex`). The variant
   `nonempty_equiv_complex_padic` derives the topological and measure hypotheses
   from the supplied data `T`: the open kernels, the quotient Haar measure and
   the openness of the norm-one set.
5. `UnequalRankCompactPairingMultiplicity`,
   `inverseFunctionals_line_of_multiplicityOne`: multiplicity one gives that
   proportionality. The step rewrites the supplied topology to the canonical
   normed topology and uses `standardCharacter (ψ.scale (-1)) n =
   inverseStandardCharacter ψ n`.

## Provenance

This is the compact/generic case of the Lemma of Jacquet, Piatetski-Shapiro and
Shalika (1983), Section 2.11, p.399, as discussed on p.403. There the line
conclusion rests on uniqueness of Whittaker functionals (Section 2.1, p.385).
Literature ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The Lean
proof follows this route through restriction induction rather than JPSS
distributions; see the module documents cited above.
