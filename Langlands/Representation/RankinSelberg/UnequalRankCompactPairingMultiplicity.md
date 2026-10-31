# The unequal-rank compact generic pairing from Whittaker multiplicity one

Author: Worker 896.

Module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity`.
This module proves that the Library proposition
`Langlands.Whittaker.MultiplicityOneStatement` implies the Library proposition
`Langlands.RankinSelberg.UnequalRankCompactGenericPairingStatement`. It does not
prove multiplicity one, so it does not prove the second statement
unconditionally.

## Main results

```lean
theorem inverseFunctionals_line_of_multiplicityOne
    (hmult : Whittaker.MultiplicityOneStatement.{uF, uW}) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W,
      IsAdmissible η → Representation.IsIrreducible η →
      ∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁

theorem unequalRankCompactGenericPairing_of_multiplicityOne
    (hmult : Whittaker.MultiplicityOneStatement.{uF, uW}) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r
```

The universes match: multiplicity one is used for representation carriers in
the same universe `uW` as the second representation of the pairing statement.

## Proofs

- The character identity reuses the published
  `Langlands.RankinSelberg.standardCharacter_scale_neg_one` from
  `FunctionalEquationStatement`. It identifies the standard character of
  `ψ.scale (-1)` with the inverse standard character of `ψ`; no duplicate
  character lemma is introduced here.
- `inverseFunctionals_line_of_multiplicityOne`:
  1. Rewrite the supplied topology `T.topology` to the canonical normed topology
     with the published `T.topology_eq_canonicalNormTopology`. Every topological
     notion in the goal, namely the continuity built into `ψ` and admissibility
     of `η`, is read through that one topology.
  2. With the canonical normed field structure, `ψ.scale (-1)` is a unitary
     additive character.
  3. By `standardCharacter_scale_neg_one`, the inverse-standard functionals of
     `ψ` are exactly the standard functionals `glFunctionals (ψ.scale (-1)) n η`
     of `ψ.scale (-1)`.
  4. Multiplicity one for `ψ.scale (-1)` gives the scalar.
- `unequalRankCompactGenericPairing_of_multiplicityOne`: apply
  `nonempty_equiv_complex_padic` of `UnequalRankCompactPairingFunctionals`.
  - Admissibility gives the smoothness it needs.
  - The line hypothesis there comes from the previous theorem.

## Provenance

The target is the compact/generic case of the Lemma of JPSS (1983), Section
2.11, p.399, discussed on p.403. There the line conclusion rests on the
uniqueness of Whittaker functionals recalled in Section 2.1 (literature ID
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). This module
is an internal assembly of Library results. It makes no further literature
claim.
