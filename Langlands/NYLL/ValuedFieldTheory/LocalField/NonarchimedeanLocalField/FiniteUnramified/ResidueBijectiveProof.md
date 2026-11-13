# Bijectivity of the residue action of an unramified extension: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement`
([target](ResidueBijectiveStatement.md), NYLL source unit M161.035) by the
theorem

```lean
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation :
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory`, the adapted source name. Its
type is the target at the same universe `u`. The theorem says: for a finite
Galois extension `L/K` of nonarchimedean local fields with a valuation
extension, whose integer ring `𝒪[L]` is the integral closure of `𝒪[K]` and
finite over it, and whose maximal ideal `𝓂[L]` has ramification index one, the
residue action `galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L :
Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` is bijective.

## Proof

The proof does not follow the source. The source combines its own injectivity
and surjectivity theorems (M161.033, M161.034), which rest on an unported chain
about inertia cardinalities and the formula `e · f = n`. Here both directions
come from Mathlib's ramification theory for a group acting on a ring
extension (`Mathlib.RingTheory.Invariant.Basic`,
`Mathlib.NumberTheory.RamificationInertia.Galois`). All auxiliary structures
are local to the proof (`let`/`have`); no instance or declaration is exported.

After `intro` of `K`, `L` and all instance binders:

### 1. The Galois action on the integer ring

Write `ρ σ := galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ`, the
published restriction of `σ ∈ Gal(L/K)` to a ring automorphism of `𝒪[L]`
(M139.002). The published evaluation
`galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` (M139.003) says that
`((ρ σ x : 𝒪[L]) : L) = σ (x : L)`.

- `φ : Gal(L/K) →* (𝒪[L] ≃+* 𝒪[L])` has `toFun := ρ`. Its two group laws
  are checked by `RingEquiv.ext` and `Subtype.ext`. After the evaluation
  lemma they reduce to `1 x = x` and `(σ * τ) x = σ (τ x)` in `L`, which
  hold by `rfl`.
- The action `MulSemiringAction Gal(L/K) 𝒪[L]` is
  `MulSemiringAction.compHom 𝒪[L] φ`, so `σ • x = ρ σ x`. Hence
  `hsmul : ((σ • x : 𝒪[L]) : L) = σ (x : L)`.
- `SMulCommClass Gal(L/K) 𝒪[K] 𝒪[L]`: in `L`, `σ (algebraMap K L a * x)
  = algebraMap K L a * σ x` by `map_mul` and `AlgEquiv.commutes`. The scalar
  action of `𝒪[K]` on `𝒪[L]` is the integer-ring algebra induced by
  `Valuation.HasExtension`, whose underlying value in `L` is
  `algebraMap K L a`; the `change` step uses this definitional unfolding.
- `SMulDistribClass Gal(L/K) 𝒪[L] L`: `σ ((r : L) * s) = σ r * σ s` by
  `map_mul` and `hsmul`.
- `Algebra.IsIntegral 𝒪[K] 𝒪[L]` is Mathlib's
  `IsIntegralClosure.isIntegral_algebra 𝒪[K] L`.
- `IsGaloisGroup Gal(L/K) 𝒪[K] 𝒪[L]` is Mathlib's
  `IsGaloisGroup.of_isFractionRing Gal(L/K) 𝒪[K] 𝒪[L] K L`. Its remaining
  inputs are found by instance search: `IsGaloisGroup Gal(L/K) K L` from
  `IsGalois K L` (Mathlib's instance `IsGaloisGroup.of_isGalois`), the fraction-field structures of the integer rings,
  `IsIntegrallyClosed 𝒪[K]` (a discrete valuation ring), and the scalar
  towers.

### 2. Separable residue fields

Mathlib's inertia formula below needs
`Algebra.HasSeparableResidueFieldsAt 𝒪[K] 𝒪[L] 𝓂[K]`. Instance search finds
it from Mathlib's instance for a perfect residue field `κ(𝓂[K])`
(`Mathlib.RingTheory.LocalRing.ResidueField.Separable`), once two finiteness
facts are recorded:

- `Finite (𝒪[K] ⧸ 𝓂[K])` is Mathlib's instance `Finite 𝓀[K]` for a
  nonarchimedean local field, since `𝓀[K]` is by definition this quotient;
- `Finite (𝓂[K]).ResidueField` follows by `Finite.of_surjective` along
  `Ideal.bijective_algebraMap_quotient_residueField`. A finite field is perfect
  (`PerfectField.ofFinite`).

### 3. Injectivity

By `injective_iff_map_eq_one`, it suffices to show that `σ = 1` whenever the
residue automorphism of `σ` is the identity.

- The published kernel characterization
  `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal`
  (M160.018) gives `ρ σ x - x ∈ 𝓂[L]` for every `x : 𝒪[L]`. With the action
  above this is exactly membership of `σ` in Mathlib's inertia subgroup
  `(𝓂[L]).inertia Gal(L/K)` (`AddSubgroup.inertia`:
  `∀ x, σ • x - x ∈ 𝓂[L]`).
- Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` gives
  `Nat.card ((𝓂[L]).inertia Gal(L/K)) = Ideal.ramificationIdxIn 𝓂[K] 𝒪[L]`.
  Its hypotheses are the Galois group structure of step 1, finiteness of
  `Gal(L/K)`, both integer rings being domains, `Module.Finite 𝒪[K] 𝒪[L]`
  (a binder of the target), flatness of `𝒪[L]` over `𝒪[K]` (found by
  instance search; mathematically, a finite torsion-free module over the
  discrete valuation ring `𝒪[K]` is free, hence flat), `𝓂[L]`
  lying over `𝓂[K]` (Mathlib's instance for valuation extensions), both ideals
  prime, and step 2.
- `Ideal.ramificationIdxIn_eq_ramificationIdx` rewrites this to
  `(𝓂[L]).ramificationIdx 𝒪[K]`, which is `1` by the field
  `maximalIdeal_ramificationIdx_eq_one` of the class
  `IsNonarchimedeanLocalField.IsUnramifiedValuedExtension` (M161.001).
- So the inertia subgroup has one element, hence is `⊥`
  (`Subgroup.card_eq_one`), and `σ = 1` by `Subgroup.mem_bot`.

### 4. Surjectivity

Let `τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]`.

- `τ'` is `τ` regarded as an `(𝒪[K] ⧸ 𝓂[K])`-algebra automorphism of
  `𝒪[L] ⧸ 𝓂[L]`. The underlying ring equivalence is `τ.toRingEquiv` at the
  quotient type, which is definitionally `𝓀[L]`. The `commutes'` field is
  checked on a representative `Ideal.Quotient.mk 𝓂[K] a` by
  `τ.commutes (IsLocalRing.residue 𝒪[K] a)`. This works because Mathlib's
  residue algebra `𝓀[K] → 𝓀[L]` and the quotient algebra
  `𝒪[K] ⧸ 𝓂[K] → 𝒪[L] ⧸ 𝓂[L]` agree definitionally on representatives.
- Mathlib's `Ideal.Quotient.stabilizerHom_surjective Gal(L/K) 𝓂[K] 𝓂[L]`
  (needing `Finite Gal(L/K)`, the `SMulCommClass` of step 1, `𝓂[L]` prime and
  lying over `𝓂[K]`, and `Algebra.IsInvariant`, part of the Galois group
  structure) gives `g` in the stabilizer of `𝓂[L]` with
  `Ideal.Quotient.stabilizerHom 𝓂[L] 𝓂[K] Gal(L/K) g = τ'`.
- The claim is that the residue action of `g` is `τ`. By `AlgEquiv.ext` and
  `IsLocalRing.residue_surjective` it suffices to compare at
  `IsLocalRing.residue 𝒪[L] a`. Evaluating the equation for `g` at
  `Ideal.Quotient.mk 𝓂[L] a`, with Mathlib's `stabilizerHom_apply`, gives
  `Ideal.Quotient.mk 𝓂[L] (g • a) = τ (residue a)`. On the other side, the
  residue automorphism of `g` is by definition the published residue
  equivalence (M160.001/M160.005), and the published residue evaluation
  `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue` (M160.002) turns
  it into `residue (ρ g a)`. Since `g • a = ρ g a` and
  `IsLocalRing.residue` is `Ideal.Quotient.mk`, the two sides agree.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings. Inspection of the theorem reported kind `theorem`,
level parameters `[u]`, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Imports

- `Mathlib.NumberTheory.RamificationInertia.Galois`: `Ideal.card_inertia_eq_ramificationIdxIn`,
  `Ideal.ramificationIdxIn_eq_ramificationIdx`;
- `Mathlib.RingTheory.Invariant.Basic`: `Ideal.Quotient.stabilizerHom_surjective`;
- `Mathlib.RingTheory.IsGaloisGroup.Basic`: `IsGaloisGroup.of_isFractionRing`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueBijectiveStatement`:
  the target, the residue homomorphism and the unramified class;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelProofs`:
  the kernel characterization and, through its imports, the published
  integer-ring and residue evaluations.

The published target, definitions and theorems are imported and used by name;
none of them is modified.

## Source correspondence and changes

The original theorem is
`LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation`
at lines 780–792 of Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean#L780-L792)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`b9c37585002a07b55997dd84ffdc7409fa5fee34fea04889196a4f617ddb909d`). Its
statement is the published target; its proof, lines 791–792, pairs the
source theorems M161.033 (line 749) and M161.034 (line 765).

Worker 3 wrote the proof above on 13 November 2026. It replaces the source
proof and uses none of the source's proof code. The source's only reused
content is the theorem name and the statement, already in the published
target. The proof reuses the published Library declarations and Mathlib by
name.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library.
