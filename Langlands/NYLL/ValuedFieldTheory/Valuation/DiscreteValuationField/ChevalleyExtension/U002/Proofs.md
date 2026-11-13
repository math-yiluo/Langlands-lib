# Base-field membership from a locally dominating valuation subring (NYLL M110.002)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.mem_base_valuationSubring_of_lift_memStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.mem_base_valuationSubring_of_lift_mem`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements`,
which is left unchanged.

## Target and mathematical meaning

The theorem keeps the statement's binders in their order: implicit fields
`K : Type u`, `L : Type v` with `[Field K] [Field L] [Algebra K L]`, implicit
`ΓK : Type w` with `[LinearOrderedCommGroupWithZero ΓK]`, then explicit
`vK : Valuation K ΓK`, `B : ValuationSubring L`, the containment
`hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring`,
the locality hypothesis
`hlocal : IsLocalHom ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB)`,
implicit `x : K` and `hxB : algebraMap K L x ∈ B.toSubring`. Its type is
`mem_base_valuationSubring_of_lift_memStatement vK B hB hlocal hxB`, which
unfolds to `x ∈ vK.valuationSubring`.

Mathematically: let `O_v ⊆ K` be the valuation ring of `vK` and let `B` be a
valuation ring of `L` that contains the image of `O_v` and such that the ring map
`O_v → B` is local (a non-unit of `O_v` never becomes a unit of `B`). Then
`B ∩ K ⊆ O_v`: an element of `K` whose image lies in `B` is already in `O_v`.

## Implemented proof

After `unfold mem_base_valuationSubring_of_lift_memStatement` the goal is
`x ∈ vK.valuationSubring`, and the rest is the unchanged source tactic proof.
Write `A := vK.valuationSubring`. By `ValuationSubring.mem_or_inv_mem`, either
`x ∈ A` (done) or `x⁻¹ ∈ A`. In the second case, `x = 0` is closed by `simp`.
Otherwise put `y := ⟨x⁻¹, _⟩ : A` and let `f : A →+* B.toSubring` be the
corestricted algebra map, which is local by `hlocal`. The element
`⟨algebraMap K L x, hxB⟩` of `B` is a left inverse of `f y` (checked by
`map_mul`, `inv_mul_cancel₀` and `map_one`), so `IsUnit (f y)` by
`IsUnit.of_mul_eq_one`; locality (`IsUnit.of_map`) gives `IsUnit y`.
`ValuationSubring.valuation_eq_one_iff` turns this into
`A.valuation x⁻¹ = 1`, hence `A.valuation x = 1` by `map_inv₀`, and
`ValuationSubring.mem_of_valuation_le_one` gives `x ∈ A`.

The proof uses only Mathlib (`Mathlib.RingTheory.Valuation.ValuationSubring`,
`Mathlib.Algebra.Group.Units.Hom` and basic field lemmas, all available through
the statement module's imports). No auxiliary declaration, instance or simp
attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean:47–76`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean#L47-L76)
(partition unit lines 47–85; docstring at lines 44–46; section variables at
lines 25 and 32–33).

| Original (namespace `ValuationTheory.DiscreteValuationField.Valuation`) | Adapted |
| --- | --- |
| Theorem `mem_base_valuationSubring_of_lift_mem`, lines 47–76 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `x ∈ vK.valuationSubring` (line 54) | `mem_base_valuationSubring_of_lift_memStatement vK B hB hlocal hxB` |
| Tactic proof, lines 55–76 | Identical, preceded by one `unfold` |

Adaptations: the namespace gains the `Langlands.NYLL` prefix; the source imports
are replaced by the single statement import; the conclusion is written as the
published statement applied to the source binders and unfolded first; the
unused universes `x y z`, the `noncomputable section` and the unused
`open ValuationTheory.DiscreteValuationField.ResidueField` are omitted.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 133's dated modification record. Worker 133 extracted
this proof directly from the pinned original and the frozen statement module;
there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`, recomputed by
Worker 133 on 13 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m110)
lists this unit in module M110 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
