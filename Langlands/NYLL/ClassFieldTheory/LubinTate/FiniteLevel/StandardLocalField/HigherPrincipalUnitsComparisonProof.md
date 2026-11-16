# Standard local field: higher principal-unit comparison proof (M335.014)

This module proves the published target
`Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnitsStatement K n`.
Its closing theorem is
`Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits`.

The complete context is explicit `(K : Type)` with `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, followed by explicit
`(n : ℕ)`. The field is in universe zero, and no additional hypothesis is
introduced. The theorem's type is the fully applied imported target.

The equality is

```lean
(higherPrincipalUnitGroup (standardLocalField K).toCompleteDVF n).map
    (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom =
  Langlands.NYLL.LocalFieldTheory.principalUnits K n
```

Thus the image of the packaged higher principal-unit subgroup under the inverse
canonical integer-unit equivalence is the topology-first principal-unit
subgroup, for every natural number `n`, including zero.

## Implemented proof

Write `e` for `standardLocalFieldIntegerUnitsEquiv K`. A local fact `hmem`
identifies membership of `e u` in the packaged subgroup with membership of `u`
in `principalUnits K n`. Its proof is `Iff.rfl`: unfolding the canonical
local-field package, its valuation subring and maximal ideal, the integer-unit
equivalence, and the two subgroup carriers yields the same congruence
`u - 1 ∈ 𝓂[K]^n`. The equivalence is induced by the identity on the underlying
field elements. No separate ideal-transport theorem is used.

The equality then follows by subgroup extensionality. In the forward direction,
a mapped-membership witness is a packaged higher principal unit `a`. The proof
first changes its membership hypothesis back to the original packaged subgroup.
It applies `hmem` to `e.symm a` and simplifies
`e (e.symm a) = a`. In the reverse direction, `hmem` shows that `e u` is in the
packaged subgroup; this supplies a map witness, with
`e.symm (e u) = u` closing its image equation.

The sole import is the published
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.PrincipalUnitComparisonStatements`.
All constructions and the statement are used by their published Lean names.
The helper is local to the proof and introduces no public declaration.

## Source and adaptations

The original is Naganori Yamaguchi's NYLL ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`,
SHA-256 `88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.
The theorem M335.014 occupies lines 204–227, with its proof at lines 210–227.
The source section context is at lines 26–38. The local membership fact
corresponds to M335.013 at lines 183–200; its proof here uses definitional
reduction in the focused published constructions instead of that source
theorem's maximal-ideal-transport argument.

The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

Worker 807 extracted this one proof, prefixed the namespace with
`Langlands.NYLL`, replaced the broad source imports by the focused target
import, and replaced the expanded equality in the theorem signature with the
fully applied published statement. The source subgroup-extensionality argument
is retained, replacing calls to M335.013 with the local `Iff.rfl` fact.
The unused `LocalFieldTheory.IsNonarchimedeanLocalField` open is omitted.
There is no change to the source parameters, hypotheses, field universe,
subgroups, maps or conclusion.

The original copyright, author and Apache-2.0 header is retained with a
modification notice. The unchanged licence and notices are
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
