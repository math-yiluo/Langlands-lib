# NYLL M351.011: the linear model `C π * X_i`

This module adapts exactly one source command of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`: the
source-private definition `linearInVariableStabilization` (unit M351.011),
published under the prescribed internal name
`Langlands.NYLL.PortInternal.M351.d011`. The five source theorems about it
and about `inVariable` that follow it (M351.012–M351.016) are not part of this
unit; they follow as separate Prop targets and proofs.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
lines 400–403. The source-file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

The source text is

```lean
private noncomputable def linearInVariableStabilization
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i
```

in the section context of source lines 28–36 and 68–70: a `noncomputable
section`, `attribute [local instance] Classical.propDecidable`, universes
`u v w`, namespaces `LubinTate.SameUniformizer`,
`open LocalFieldTheory.DiscreteValuationField`, and

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]
```

## Source correspondence

| Source unit | Original declaration and lines | Adapted declaration (Lean lines) |
| --- | --- | --- |
| M351.011 | `LubinTate.SameUniformizer.linearInVariableStabilization` (private), 400–403 | `Langlands.NYLL.PortInternal.M351.d011` (46–51, docstring included) |

**Elaborated source type.** Lean includes a section variable in a definition
only when the header or body uses it, together with instance arguments all of
whose variables are included; the remaining ones are dropped. In the source,
the explicit binder `(π : F.valuationSubring)` shadows the section variable
`{π}`, and nothing in the header or body needs `Fintype σ`. A private probe
reproducing the source section verbatim (lines 28–36, 68–70 and 400–403,
with the published `LocalField`) printed

```text
private def …linearInVariableStabilization.{u, v, w} : {K : Type u} →
  [inst : Field K] → {F : LocalField K} → {σ : Type w} →
  F.valuationSubring → σ → MvPowerSeries σ F.valuationSubring :=
fun {K} [Field K] {F} {σ} π i => MvPowerSeries.C π * MvPowerSeries.X i
```

So although the source command sits in the section with `[Fintype σ]`, its
effective type has no `Fintype σ` (and no `Finite σ`) argument and no
section `π`. This is also why the following source theorems may write
`omit [Fintype σ] in` and still use it. The adapted module declares exactly
the variables of this elaborated type,

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {σ : Type w}
```

followed by the source binders `(π : F.valuationSubring) (i : σ)`. Hence
`d011` has the universe parameters `u v w` in this order and the telescope
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {σ : Type w}
(π : F.valuationSubring) (i : σ)`, with the same binder kinds and order as
the source. No finiteness premise is imposed on `σ`. A focused check in the
probe confirmed this by assigning `@d011` to the source type
`∀ {K : Type u} [Field K] {F : LocalField.{u, v} K} {σ : Type w},
F.valuationSubring → σ → MvPowerSeries σ F.valuationSubring` and by proving
`@linearInVariableStabilization.{u, v, w} = @d011.{u, v, w}` with `rfl`.

`LocalField` resolves to the shared published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K`
(M334.001) and `F.valuationSubring` to its published accessor (M334.003).

## Mathematical meaning

Write `O = F.valuationSubring`, the valuation subring of the local field
package `F` on `K`. For `π ∈ O` and a variable index `i : σ`,
`d011 π i : MvPowerSeries σ O` is the series `π·X_i`, written as
`MvPowerSeries.C π * MvPowerSeries.X i`: the constant series `π` times the
`i`-th coordinate variable. Its only nonzero coefficient is `π` at the
exponent `Finsupp.single i 1` (if `π ≠ 0`). The element `π` is arbitrary in
`O`; no uniformizer hypothesis is added, as in the source. `σ` is an
arbitrary type in its own universe `w`.

In the source this is the linear part of `inVariable ebar i = ebar(X_i)` for a
Lubin–Tate series `ebar` whose linear coefficient is `π`; the next source
units show that `ebar(X_i) - π·X_i` has order at least two, and the later
coefficient computations of the module compare substitutions into
`ebar(X_i)` with substitutions into `π·X_i`. The declaration is
`noncomputable`, as in the source.

## Dependencies

The module imports only

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`
  (published M334.001–M334.005: `LocalField` and `valuationSubring`), and
- `Mathlib.RingTheory.MvPowerSeries.Basic` (`MvPowerSeries`, `C`, `X` and
  the ring structure).

The source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`
and `Mathlib.RingTheory.MvPowerSeries.Trunc`; none of their declarations
occurs in this definition, and the successful focused check of this module
with the two imports above shows that they suffice.

## Modifications

All modifications, by Worker 491 on 14 November 2026:

1. the source-private name `LubinTate.SameUniformizer.linearInVariableStabilization`
   is replaced by `Langlands.NYLL.PortInternal.M351.d011`, and the
   `private` modifier is removed so that later port units can import it;
2. the opened namespace is written `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`;
3. the source imports are replaced by the two focused imports above;
4. only the section variables of the elaborated source type are declared: the
   shadowed section variable `{π}` and the unused instance `[Fintype σ]`,
   which Lean drops from the source definition, are not declared;
5. the local instance `Classical.propDecidable`, `open scoped BigOperators`
   and all other source declarations are omitted; none is used by this
   definition, whose type and body involve no decidability instances;
6. a modification notice in the header, a new module docstring and a
   declaration docstring naming M351.011.

The binders, their order and kinds, the result type and the body
`MvPowerSeries.C π * MvPowerSeries.X i` are unchanged. This unit introduces
no instances and no theorems.

## License

The original 2026 copyright, Apache-2.0 release line and author header are
preserved verbatim. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
