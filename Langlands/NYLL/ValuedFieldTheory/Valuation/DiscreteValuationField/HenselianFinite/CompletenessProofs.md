# Proofs of adic completeness under linear equivalence and for finite modules

This module proves the two closed proposition targets published in
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.Statements`.
Both targets are stated with independent ring and module universes. Both
proofs keep those universes independent.

| Theorem (namespace `Langlands.NYLL.ValuationTheory.DiscreteValuationField`) | Universe parameters | Complete unapplied type |
| --- | --- | --- |
| `isAdicComplete_of_linearEquiv` | `u, v, w` | `IsAdicCompleteOfLinearEquivStatement.{u, v, w}` |
| `isAdicComplete_of_moduleFinite` | `u, v` | `IsAdicCompleteOfModuleFiniteStatement.{u, v}` |

Each theorem's type is the named target constant itself, with its universe
parameters in order and no further arguments. Every mathematical parameter
(the ring, the modules, their structures, the ideal, the equivalence and the
hypotheses) is bound inside the target. The proofs open the target with
`intro` and use only the hypotheses it supplies.

`IsAdicComplete I X` is Mathlib's algebraic class: `X` is Hausdorff and
precomplete for the filtration `I ^ n • ⊤`. Both proofs use the criterion
`AdicCompletion.of_bijective_iff`: `IsAdicComplete I X` holds exactly when the
canonical `R`-linear map `AdicCompletion.of I X : X → AdicCompletion I X` is
bijective. They also use its converse `AdicCompletion.of_bijective`.

## Linear equivalence: `isAdicComplete_of_linearEquiv`

The target supplies `R : Type u`, `M : Type v`, `N : Type w`, the commutative
ring and module structures, an ideal `I : Ideal R`, an `R`-linear equivalence
`e : M ≃ₗ[R] N`, and `IsAdicComplete I M`. It concludes
`IsAdicComplete I N`.

By `AdicCompletion.of_bijective_iff` it suffices to show that
`AdicCompletion.of I N` is bijective. The proof first shows that, as functions
on `N`,

```
AdicCompletion.of I N = AdicCompletion.congr I e ∘ AdicCompletion.of I M ∘ e.symm.
```

Here `AdicCompletion.congr I e` is the linear equivalence of completions
induced by `e`. To check this at a point `y`, unfold `congr I e` to
`AdicCompletion.map I e` (`AdicCompletion.congr_apply`). Then
`AdicCompletion.map_of` rewrites `map I e (of I M (e.symm y))` to
`of I N (e (e.symm y))`, and `e (e.symm y) = y`. `simp` does these steps. The
right-hand side composes three bijections: `e.symm`, `AdicCompletion.of I M`
(bijective by `AdicCompletion.of_bijective`, since `M` is complete), and the
equivalence `AdicCompletion.congr I e`. So `AdicCompletion.of I N` is
bijective.

The proof makes no assumption on `R`, `M` or `N` beyond those in the target.
The three universes `u`, `v`, `w` stay unrelated.

## Same-universe finite modules: private helper

`isAdicComplete_of_moduleFinite_sameUniverse` is a `private` theorem used only
by the next proof. It is not a published target or a public declaration. It
takes `R M : Type u` in one universe, `CommRing R`, `AddCommGroup M`,
`Module R M`, `I : Ideal R`, `IsNoetherianRing R`, `Module.Finite R M` and
`IsAdicComplete I R`, and concludes `IsAdicComplete I M`.

The proof needs a shared universe because Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M :
AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M` is stated
in the section `Noetherian` of
`Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`. That section rebinds
`R : Type u` and `M : Type u` (lines 218–219). This equivalence is the bijective
canonical map `AdicCompletion.ofTensorProduct I M`, which sends `r ⊗ₜ x` to
`r • AdicCompletion.of I M x`.

The proof builds the composite `R`-linear equivalence

```
e : M ≃ₗ[R] AdicCompletion I M :=
  (TensorProduct.lid R M).symm
    ≪≫ₗ TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M)
    ≪≫ₗ (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
```

It sends `x` to `1 ⊗ₜ x`, then to `AdicCompletion.of I R 1 ⊗ₜ x`, and then
to `AdicCompletion.of I R 1 • AdicCompletion.of I M x`. The middle step uses
`AdicCompletion.ofLinearEquiv I R`, which is `AdicCompletion.of I R` packaged
as a linear equivalence because `R` is `I`-adically complete. The equality
`AdicCompletion.of I R 1 = 1` is proved with `AdicCompletion.algebraMap_apply`
and `map_one`. With it, `simp` shows that `e` and `AdicCompletion.of I M` are
equal as functions. It uses `AdicCompletion.ofTensorProduct_tmul` and
`one_smul`. Since `e` is an equivalence, `AdicCompletion.of I M` is bijective,
and `AdicCompletion.of_bijective_iff` gives `IsAdicComplete I M`.

## Finite modules with independent universes: `isAdicComplete_of_moduleFinite`

The target supplies `R : Type u`, `M : Type v`, `CommRing R`,
`AddCommGroup M`, `Module R M`, `I : Ideal R`, `IsNoetherianRing R`,
`Module.Finite R M` and `IsAdicComplete I R`. It concludes
`IsAdicComplete I M`.

1. `Module.Finite.small R M` gives `Small.{u} M`. A finite module over a ring
   in `Type u` is `u`-small (the instance `Small.{u} R` holds because
   `R : Type u`).
2. Mathlib's `Shrink.{u} M : Type u` carries the transferred `R`-module
   structure from `Mathlib.Algebra.Module.Shrink`.
   `Shrink.linearEquiv R M : Shrink.{u} M ≃ₗ[R] M` is an `R`-linear
   equivalence. `Module.Finite.equiv` along its inverse gives
   `Module.Finite R (Shrink.{u} M)`.
3. Now `R` and `Shrink.{u} M` both lie in `Type u`. The private helper gives
   `IsAdicComplete I (Shrink.{u} M)` for the same ideal `I`.
4. `isAdicComplete_of_linearEquiv.{u, u, v}`, applied to `R`,
   `Shrink.{u} M`, `M`, `I` and `Shrink.linearEquiv R M`, transports
   completeness to `M`. The ring and module universes `u` and `v` are not
   identified.

The module structure on `M` and the ideal `I` are those of the target
throughout. The proof adds no hypothesis. It assumes nothing Henselian,
local, topological, discrete-valuation or field-theoretic, and no
residue-field finiteness.

## Source correspondence

The proofs adapt Naganori Yamaguchi's NYLL ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.

| Source unit | Source declaration and lines | Here |
| --- | --- | --- |
| M105.001 | `ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv`, [`AdicPower.lean`, lines 22–52](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean#L22-L52) | `isAdicComplete_of_linearEquiv` |
| M191.013 | `ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite_sameUniverse`, [`HenselianFinite.lean`, lines 224–255](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean#L224-L255) | private `isAdicComplete_of_moduleFinite_sameUniverse` |
| M191.014 | `ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite`, [`HenselianFinite.lean`, lines 257–275](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean#L257-L275) | `isAdicComplete_of_moduleFinite` |

The public theorem names are the source names with the `Langlands.NYLL`
namespace prefix. Their statements are the published closed targets. The
source states the same assertions with implicit types and explicit `I`
(and `e`).

The implemented proofs differ from the source as follows:

- M105.001: the source proves injectivity and surjectivity of
  `AdicCompletion.of I N` separately, each by conjugating with
  `AdicCompletion.congr I e` and using `AdicCompletion.map_of`. Here the
  conjugation is a single function equation, and the proof composes the three
  bijections. It uses the same Mathlib lemmas: `AdicCompletion.of_bijective_iff`,
  `AdicCompletion.of_bijective`, `AdicCompletion.congr` and
  `AdicCompletion.map_of`.
- M191.013: the source builds the same composite equivalence and identifies
  its forward map with `AdicCompletion.of I M` by applying the inverse of the
  tensor equivalence and `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of`.
  Here `simp` evaluates the forward map directly with
  `AdicCompletion.ofTensorProduct_tmul`. The proof of
  `AdicCompletion.of I R 1 = 1` follows the source. The helper is `private`
  and its binder order puts the module structures before `I`.
- M191.014: the source makes the `Small` and `Module.Finite` instances with
  `let`. It obtains finiteness of `Shrink.{u} M` with
  `Module.Finite.of_surjective` along the inverse of `Shrink.linearEquiv R M`.
  Here they are `have` hypotheses, and finiteness comes from
  `Module.Finite.equiv` along the same inverse equivalence. The final transport
  through the linear-equivalence theorem is the source's.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.Statements`:
  the two published targets. Their Lean and Markdown are unchanged.
- `Mathlib.Algebra.Module.Shrink`: the module structure on `Shrink` and
  `Shrink.linearEquiv`.
- `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`:
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` and
  `AdicCompletion.ofTensorProduct_tmul`. Through its imports it also provides
  `AdicCompletion.congr`, `AdicCompletion.map_of` (`Functoriality`),
  `AdicCompletion.algebraMap_apply` (`Algebra`) and the completeness criterion
  (`Basic`).
- `Mathlib.RingTheory.Finiteness.Small`: `Module.Finite.small`.

No NYLL module is imported. The proofs do not use the source's
`Henselian` import, the linear-equivalence chain M191.001–M191.012, or
`Mathlib.RingTheory.AdicCompletion.Noetherian` and `Mathlib.RingTheory.Nakayama`.

## Scope

The module adds two public theorems and one private helper, and no instance,
definition or axiom. Kernel inspection lists only `propext`,
`Classical.choice` and `Quot.sound`. It does not duplicate Mathlib's
`IsAdicComplete.map_algebraMap_iff` or `IsAdicComplete.congr_ringEquiv`, which
cover the source's mapped-ideal and ring-equivalence lemmas M105.006 and
M105.007. It proves nothing about Henselian rings (M191.015 and later), finite
integral closures, valuation extensions, inertia or reciprocity.

## Source record, attribution and modifications

The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The original files have SHA256
`df1f92c6b85a87ad4a27c319302f267a717b7f82c1cce10167c56b1c4793232d`
(`AdicPower.lean`) and
`ba8c98a9f27133d8ba9637baf667805e783a3999654b1711e5f72601e749aab1`
(`HenselianFinite.lean`). Both values were rechecked against the pinned
snapshot when this proof was written. The attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`) has a
`ValuedFieldTheory` third-party table, `ANTHROPIC_FLT_ATTRIBUTION.md`, that
lists neither file, so no further third-party attribution applies. No
applicable erratum was found. The retained feasibility patch P2 for
`HenselianFinite.lean` changes only M191.004 and does not affect these proofs.

The Lean file keeps the original copyright and author header (copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi, assisted by OpenAI Codex;
Apache-2.0), followed by a modification record. The unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply.

Worker 874 adapted the three source proofs on 28 October 2026 in these ways:

- proved the published closed targets;
- added the namespace prefix;
- made M191.013 a private helper;
- restructured the M105.001 and M191.013 proofs as described above;
- replaced `Module.Finite.of_surjective` with `Module.Finite.equiv` in
  M191.014;
- reduced the imports to the four listed above;
- wrote this Markdown.

No other worker's adapted Lean content was used. The module targets approved
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
