# Ramification index times inertia degree: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrankStatement`
([target](RamificationInertiaDegreeStatement.md), NYLL source unit M138.028) by the
theorem

```lean
theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank :
    maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrankStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory`, the adapted source name. Its type
is the target at the same universe `u`. The theorem says: for a finite extension
`L/K` of nonarchimedean local fields with a valuation extension, whose integer
ring `𝒪[L]` is a finite `𝒪[K]`-module, the ramification index
`Ideal.ramificationIdx' 𝓂[K] 𝓂[L]` times the inertia degree
`(𝓂[L]).inertiaDeg 𝒪[K]` equals `Module.finrank K L`.

## Proof

The proof is the source proof after an opening `intro`. It specializes Mathlib's
formula `∑ e(q) f(q) = rank` over the primes `q` above `𝓂[K]` to the single
prime `𝓂[L]`.

1. `intro K L` followed by anonymous introductions of the twelve instance
   binders of the target; then `classical`.
2. `FaithfulSMul 𝒪[K] 𝒪[L]` is Mathlib's
   `FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L`: `𝒪[K] → 𝒪[L]` is
   injective because its composite with `𝒪[L] → L` factors through the
   injective maps `𝒪[K] → K → L`. Instance search supplies the fraction-field
   structures `IsFractionRing 𝒪[K] K`, `IsFractionRing 𝒪[L] L` and the scalar
   towers.
3. `hp : 𝓂[K] ≠ ⊥` is Mathlib's `IsDiscreteValuationRing.not_a_field 𝒪[K]`;
   the integer ring of a nonarchimedean local field is a discrete valuation ring.
4. `hprimes : (𝓂[K]).primesOver 𝒪[L] = {𝓂[L]}` is Mathlib's
   `IsLocalRing.primesOver_eq hp`. It uses that `𝒪[L]` is local and a Dedekind
   domain (a discrete valuation ring, hence a principal ideal domain), the
   faithfulness of step 2, `Module.Finite 𝒪[K] 𝒪[L]` (a binder of the target)
   and maximality of `𝓂[K]`.
5. From `hprimes`, `hq` says every `q` in the subtype of primes over `𝓂[K]`
   has underlying ideal `𝓂[L]`, and a local `Unique` instance on that subtype has
   default element `𝓂[L]`.
6. Two rewrites change the goal to
   `(𝓂[L]).ramificationIdx 𝒪[K] * (𝓂[L]).inertiaDeg 𝒪[K] = Module.finrank 𝒪[K] 𝒪[L]`:
   - Mathlib's `Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp` identifies
     `Ideal.ramificationIdx' 𝓂[K] 𝓂[L]` with `(𝓂[L]).ramificationIdx 𝒪[K]`, for
     a Dedekind domain `𝒪[L]` torsion-free over the domain `𝒪[K]`, with `𝓂[L]`
     prime and lying over `𝓂[K]` (Mathlib's instance for valuation extensions)
     and `𝓂[K] ≠ ⊥`;
   - Mathlib's `IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L` gives
     `Module.finrank K L = Module.finrank 𝒪[K] 𝒪[L]`.
7. Mathlib's `Ideal.sum_ramification_inertia_eq_finrank 𝓂[K] 𝒪[L]` gives
   `∑ q : (𝓂[K]).primesOver 𝒪[L], q.ramificationIdx 𝒪[K] * q.inertiaDeg 𝒪[K] =
   Module.finrank 𝒪[K] 𝒪[L]`. Its hypotheses are that `𝒪[K]` is a domain,
   `Module.Finite 𝒪[K] 𝒪[L]`, flatness of `𝒪[L]` over `𝒪[K]` (found by instance
   search; mathematically, a finite torsion-free module over the discrete
   valuation ring `𝒪[K]` is free, hence flat), and a `Fintype` instance on the
   subtype, which comes from the `Unique` instance of step 5.
   `simpa only [Fintype.sum_unique, hq]` reduces the sum to its single term at
   `𝓂[L]`, which is the goal.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no
errors or warnings. Inspection of the theorem reported kind `theorem`, level
parameters `[u]`, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Imports

- `Mathlib.RingTheory.DedekindDomain.Basic`: `IsLocalRing.primesOver_eq`;
- `Mathlib.RingTheory.RamificationInertia.Basic`:
  `Ideal.sum_ramification_inertia_eq_finrank`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationInertiaDegreeStatement`:
  the target, and through its Mathlib imports the remaining lemmas used above.

The published target is imported and used by name; it is not modified.

## Source correspondence and changes

The original theorem is
`LocalFieldTheory.maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank` at lines
356–380 (docstring at 356, theorem at 358, proof at 367–380) of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L356-L380)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`). Its
statement is the published target.

Worker 4699 made these changes on 15 November 2026:

1. Prefix the namespace with `Langlands.NYLL`; keep the theorem name.
2. State the theorem's type as the published closed proposition
   `maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrankStatement.{u}` instead
   of the source binders and conclusion, and introduce the binders with `intro`.
3. Keep the fourteen source proof lines unchanged.
4. Keep the source docstring and add one sentence naming the target.
5. Replace the source imports by the published statement module and the two
   Mathlib modules above, and omit the source's `noncomputable section`.
6. Keep the original copyright and author header verbatim and add the
   modification record.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library.
