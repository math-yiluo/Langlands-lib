# Actual Herbrand functions and upper ramification groups

This module adapts exactly M305.004, M305.005 and M305.012 from Naganori
Yamaguchi's *ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/HerbrandFunction.lean).
The declarations occupy lines 70–86 and 156–164. The whole original
file, including its ambient telescope, finite-dimensional section and
local `generalDVFGalFintype` instance, was read directly. Its SHA-256 is
`a094355ce3645fe924eb8575233a874ca16007f91ab9bafe99f13c33cd3a878c`.

## Complete interfaces and defining expressions

All three declarations lie in
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`.
In that namespace their complete interfaces and bodies are:

```lean
noncomputable def herbrandFunctionOfUniqueExtension
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (s : ℝ) : ℝ :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) s

noncomputable def inverseHerbrandFunctionOfUniqueExtension
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (t : ℝ) : ℝ :=
  Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) t

noncomputable def upperRamificationGroupOfUniqueExtension
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) (t : ℝ) : Subgroup Gal(L/K) :=
  lowerRamificationGroup
    (base := base) (target := target) huniq
    (inverseHerbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq t)
```

The source's `noncomputable section` makes the last definition
noncomputable as well. The four universes `u, v, w, x` are independent:
the fields live in `u, w`, and their valuation value groups in `v, x`.
The final `x` in the uniqueness predicate specifies the comparison
valuation universe, as in the source. Both fields and DVFs are implicit;
their field structures, algebra and valuation-extension instance are
supplied; `huniq` and the real argument are explicit. There are no other
parameters. In particular, no `FiniteDimensional K L`, `Finite Gal(L/K)`
or `Fintype Gal(L/K)` instance enters these interfaces.

The first two functions apply the published normalized generic function
and the generic
[`inverseHerbrandFunction`](../../Herbrand/Function/InverseDefinition.md)
to the same published
[`lowerRamificationFiltrationOfUniqueExtension`](LowerFiltration.md)
and then the real argument. That filtration's natural level `n` is
the actual `lowerRamificationGroup huniq (n : ℝ)`, with the same supplied
`base` and `target`. Its published normality and antitonicity proofs
are reused unchanged.

The third construction evaluates the actual real lower-group family
at the actual inverse-function index. Its result is a subgroup of
Mathlib's actual algebra automorphism group `Gal(L/K) = L ≃ₐ[K] L`,
with its standard composition law. Neither valuations nor fields
are replaced, transported or chosen by these definitions.

## Definition scope and later laws

These are data definitions for every supplied unique extension of the
stated DVFs. They require no completeness, Galois, residue-separability,
eventual-triviality or inverse-law premise. The source forward-function
docstring mentions “separable-residue assumptions”; that phrase is
removed because there is no such assumption in its type.

The generic inverse uses Mathlib's `Function.invFun`, which is defined
without injectivity or surjectivity. Consequently these declarations
alone do not prove that the forward and inverse functions are mutually
inverse. The generic finite-group analytic results support later
finite-scope inverse laws; finite-dimensionality can supply the finite
actual automorphism group when such laws need it. Those hypotheses
are unnecessary for the four data definitions in this unit.

Only M305.004, M305.005 and M305.012 are added by this module; M303.029
is added by its generic companion. Generic inverse equations and order
isomorphisms, actual evaluation/inverse/monotonicity laws, upper-group
laws, host inertia, filtered reciprocity and final reciprocity
remain separate statement/proof work.

## Exact source map and modifications

| Unit and original declaration | Adapted declaration |
| --- | --- |
| M305.004, `RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension`, lines 73–78 | `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension` |
| M305.005, `RamificationTheory.HilbertRamification.Higher.inverseHerbrandFunctionOfUniqueExtension`, lines 81–86 | `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.inverseHerbrandFunctionOfUniqueExtension` |
| M305.012, `RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension`, lines 158–164 | `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension` |

The namespace gains `Langlands.NYLL`. The uniqueness predicate and
generic function names are explicitly qualified under that prefix.
All three defining expressions, universe dependencies, binder kinds
and argument order are retained. The first docstring is corrected
as described above; the inverse and upper-group docstrings are
preserved. The original unused namespace opening is omitted.

The original wholesale imports are replaced by exactly:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.InverseDefinition`,
  which supplies the new generic inverse and the published forward function.
- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LowerFiltration`,
  which supplies the published actual lower filtration and actual real
  lower-group family.

The source section's `[FiniteDimensional K L]` and local
`generalDVFGalFintype` are unused by these bodies and are omitted.
The source `noncomputable section` and individual function modifiers
are retained. No new instance or auxiliary declaration is added.
Interleaved theorems are omitted and no analytic proof module is
imported. The published dependencies and their paired documentation
are unchanged. The public M305 partition records no patch10 change;
its conservative source-order and module-completion edges do not
add mathematical premises to the extracted bodies.

Existing host `Langlands.Ramification.Padic.herbrandPsi` and the
Herbrand polygon order isomorphism have a different arithmetic/cutoff
interface. They do not define this `Function.invFun` on an arbitrary
supplied filtration. This extraction reuses the published NYLL
functions, actual lower groups and Mathlib's construction directly.

## Sources, license and authorship

The registered original is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the
original path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or supplied-Library `notes/errata` directory
was present at preparation.

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). Apache-2.0 applies. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned originals,
with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Their inherited notices are preserved unchanged. The root NOTICE inventory
has no entry for this source file.

Worker 106 contributed the source/interface extraction and reuse analysis
in the task contract. Worker 1199 independently checked the original
source, published interfaces and dependencies, implemented the extraction
and wrote this companion on 2 November 2026. The Lean header records the
modifications. The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, distinct from the source's
Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
