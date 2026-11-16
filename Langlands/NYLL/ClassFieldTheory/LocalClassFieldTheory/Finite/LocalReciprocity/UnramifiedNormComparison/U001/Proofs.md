# Field norms lie in the unramified norm subgroup: proof

This module proves the published closed target
`Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_le_unramifiedNormSubgroupStatement`
([target](../SubgroupStatements.md), NYLL source unit M267.001 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m263-m269.md#m267))
by the theorem

```lean
theorem localNormSubgroup_le_unramifiedNormSubgroup :
    localNormSubgroup_le_unramifiedNormSubgroupStatement
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name. Its
type is exactly the target, which has no universe parameters (`K L : Type`).

The theorem says: let `L/K` be a finite Galois extension of nonarchimedean local
fields (`K L : Type`), with the valuation of `L` extending that of `K`, `𝒪[L]` the
integral closure of `𝒪[K]` in `L` and finite over `𝒪[K]`, and with an instance of
the published class `IsUnramifiedValuedExtension K L` (M161.001). Then every norm
`N_{L/K}(y)` of a unit `y` of `L` lies in `unramifiedNormSubgroup K [L : K]`, that
is, its normalized valuation `v_K(N_{L/K}(y))` is divisible by `[L : K]`. Here
`localNormSubgroup K L` (M093.001) is by definition the range of the norm
homomorphism `normUnits K L : Lˣ →* Kˣ` (M092.002), and
`unramifiedNormSubgroup K n` (M266.011) is the subgroup of units `x` of `K` with
`(n : ℤ) ∣ valuationMap K (Additive.ofMul x)`.

## Proof

The proof is the source proof after an opening `intro` of the target's binders.
Mathematically: for a unit `y` of `L`, `v_K(N(y)) = f · v_L(y)` with `f` the
residue degree, and `f = [L : K]` because `L/K` is unramified; so `[L : K]` divides
`v_K(N(y))`. The Library proofs it uses are applied to `K` and `L`, and their
instance arguments are found by instance search among the introduced binders.

1. `intro K L`, anonymous introductions of the fifteen instance binders of the
   target, then `x hx` with `hx : x ∈ localNormSubgroup K L`.
2. `obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx`: since `localNormSubgroup K L`
   is by definition `(normUnits K L).range`, Mathlib's `MonoidHom.mem_range` gives a
   unit `y` of `L` with `normUnits K L y = x`, and `x` is replaced by
   `normUnits K L y`.
3. `apply (mem_unramifiedNormSubgroup_iff K (Module.finrank K L) _).2` (M266.012,
   [proof](../../../Existence/UnramifiedNormSubgroup/U012/Proofs.md)) reduces the
   goal to `(Module.finrank K L : ℤ) ∣ valuationMap K (Additive.ofMul (normUnits K L y))`.
4. `rw [valuationMap_apply]` (M134.004,
   [proof](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence/U004/Proofs.md))
   replaces `valuationMap K` by the normalized valuation `v K`; the following
   `change` restates the goal in the same form,
   `(Module.finrank K L : Int) ∣ v K (Additive.ofMul (LocalFieldTheory.normUnits K L y))`.
5. Two rewrites:
   - `v_normUnits_eq_residue_finrank_mul_of_isSeparable K L` (M162.019,
     [proof](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation/U019/Proofs.md))
     replaces `v K (Additive.ofMul (normUnits K L y))` by
     `(Module.finrank 𝓀[K] 𝓀[L] : Int) * v L (Additive.ofMul y)`. For each unit
     `x` of `L` the theorem's type is the published proposition
     `v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement K L x`, whose
     body is this equation; `rw` unfolds it and finds `x := y`. Its instance
     argument `Algebra.IsSeparable K L` is found by instance search from
     `IsGalois K L` through Mathlib's instance `IsGalois.to_isSeparable`;
   - `unramifiedValuation_residue_finrank_eq_finrank K L` (M161.003,
     [proof](../../../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified/ResidueDegreeProof.md))
     replaces `Module.finrank 𝓀[K] 𝓀[L]` by `Module.finrank K L`.
6. The goal is now
   `(Module.finrank K L : Int) ∣ (Module.finrank K L : Int) * v L (Additive.ofMul y)`,
   closed by Mathlib's `dvd_mul_right _ _`.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no
errors or warnings. Inspection of the theorem reported kind `theorem`, no level
parameters, and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.SubgroupStatements`:
  the target, with `localNormSubgroup`, `unramifiedNormSubgroup` and
  `IsUnramifiedValuedExtension` through its imports;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U012.Proofs`:
  the M266.012 proof `mem_unramifiedNormSubgroup_iff`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs`:
  the M134.004 proof `valuationMap_apply`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U019.Proofs`:
  the M162.019 proof `v_normUnits_eq_residue_finrank_mul_of_isSeparable`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueDegreeProof`:
  the M161.003 proof `unramifiedValuation_residue_finrank_eq_finrank`.

The Mathlib lemmas `MonoidHom.mem_range` and `dvd_mul_right` and the instance
`IsGalois.to_isSeparable` come through these imports. The four proofs are
published Library results imported by Lean name; this module does not copy them.
The published target is imported and used by name; it is not modified.

## Source correspondence and changes

The original theorem is
`LocalClassFieldTheory.localNormSubgroup_le_unramifiedNormSubgroup` at lines 47–59
(docstring at 46, statement at 47–49, proof at 50–59, section variables at 34–44)
of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean#L46-L59)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`). Its
statement, closed over the section variables, is the published target. The
source proof uses the source theorems `mem_unramifiedNormSubgroup_iff` (M266.012),
`valuationMap_apply` (M134.004), `v_normUnits_eq_residue_finrank_mul_of_isGalois`
(M162.025, `SeparableNormValuation.lean` line 703) and
`unramifiedValuation_residue_finrank_eq_finrank` (M161.003).

Worker 396 made these changes on 15 November 2026:

1. Prefix the namespace with `Langlands.NYLL`; keep the theorem name.
2. State the theorem's type as the published closed proposition
   `localNormSubgroup_le_unramifiedNormSubgroupStatement` instead of the source
   section variables and conclusion, and introduce the section variables in the
   proof's opening `intro` together with the source's `x hx`.
3. Replace the source call `v_normUnits_eq_residue_finrank_mul_of_isGalois K L` by
   `v_normUnits_eq_residue_finrank_mul_of_isSeparable K L`. The M162.025 theorem
   has no proof in the Library; its source proof (lines 703–717) is exactly
   `v_normUnits_eq_residue_finrank_mul_of_isSeparable K L x`, with the separability
   instance found from `IsGalois K L`, so the rewrite uses the same equation.
4. Keep the other source proof lines (51–56, 58–59) unchanged.
5. Keep the source docstring and add one sentence naming the target.
6. Replace the source imports by the published statement module and the four
   proof modules above, and omit the source's `noncomputable section`.
7. Keep the original copyright and author header verbatim and add the
   modification record.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`. The
Apache-2.0 [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library.
