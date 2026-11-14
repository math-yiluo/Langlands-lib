# NYLL M231.018: finiteness of principal-unit subquotients (target)

For a complete discrete valuation field `F` with finite residue field, and
for any two levels `m` and `n`, the quotient of the level-`m` principal units
`U^m` by those of its elements that lie in `U^n` is finite. This pair supplies
only the proposition. Its proof is separate work.

## Exact target

The declaration is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residueStatement`,
a definition with value in `Prop`. Its universe parameters are `u` and `v`.
Its parameters, in order, are:

1. `{K : Type u}` (implicit) and `[Field K]`;
2. `(F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)`
   (explicit), the shared complete-DVF package;
3. `[Finite F.residueField]`, the instance hypothesis that the residue field
   is finite;
4. `(m n : ℕ)` (explicit).

Its value is

```lean
Finite (higherPrincipalUnitGroup F m ⧸
  (higherPrincipalUnitGroup F n).subgroupOf (higherPrincipalUnitGroup F m))
```

Here `higherPrincipalUnitGroup F k` is the published concrete subgroup
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`
of `F.valuationSubringˣ`, with carrier
`{u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ k}`. It comes from
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`
(NYLL M225.001), the only import. `F.residueField` is the published
complete-DVF projection `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.residueField`,
which reaches this module through that import.

`Subgroup.subgroupOf` gives the subgroup of the group `↥(higherPrincipalUnitGroup F m)`
consisting of the elements whose image in `F.valuationSubringˣ` lies in
`higherPrincipalUnitGroup F n`. So it is `U^n ∩ U^m` viewed inside `U^m`. The quotient `⧸` is
Mathlib's quotient of a group by a subgroup. `Finite` is Mathlib's
proposition-valued finiteness class for that type.

No inequality between `m` and `n` is assumed. When `n ≤ m`, `U^m ⊆ U^n`,
so the subgroup is all of `U^m` and the quotient has one element. When `m ≤ n` the
quotient is `U^m/U^n`. The finite-residue-field instance does not occur in
the proposition body. It is kept because the source theorem has it and the
source proof uses it. The universes `u` and `v` are independent, as in the
source.

## Source and modifications

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`
(file SHA-256 `415353484b021d45b0a0d02fe3d57049ec1c92dc8ca8da27477e403b0d1f0604`).
The declaration is NYLL M231.018,
`LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue`.
Its docstring is at lines 337–339, its signature and conclusion at lines 340–344,
and its proof at lines 345–369. The task text says the proof runs "through
372". Lines 370–372 hold a blank line and the opening of the docstring for the
following instance M231.019, so the proof itself ends at line 369. The context
in force is at these lines:

- `namespace LocalFieldTheory`, line 21;
- `open ValuationTheory`, line 23;
- `noncomputable section`, line 25;
- `universe u v`, line 29;
- namespaces `DiscreteValuationField` and `CompleteDVF`, lines 31–32;
- `variable {K : Type u} [Field K]`, line 34;
- `namespace higherPrincipalUnitGroup`, line 36;
- `variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)`,
  line 40.

The source file is in registered source `external-lean-reuse-snapshots-2026-10-21`.
Its license, notice and attribution files are in registered source
`nyll-classfieldtheory-fbd320cd-supplement`.

Worker 299 drafted this pair, and Worker 476 revised and submits it. The
changes from the source are:

- The namespace has the prefix `Langlands.NYLL`. The source's
  `ValuationTheory.…CompleteDVF` therefore resolves to the published
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
- The theorem becomes a `Prop`-valued `def` with the suffix `Statement`. Its
  body is the source conclusion, unchanged.
- The source `variable` declarations at lines 34 and 40 become explicit binders
  on the definition. Their order, explicitness and universe annotations are
  the same as in the source: `K`, the field instance, `F`, the residue
  instance, `m`, `n`.
- The source imports are replaced by the one published module holding the
  M225.001 subgroup construction. The source's `open` commands and
  `noncomputable section` are not needed for this proposition and are left out.
- The module comment and the docstring are new.

There is no new hypothesis, no `m ≤ n` restriction, no helper declaration and
no global instance. This pair leaves out the source proof (lines 345–369) and
the later finite instances, such as M231.019 `principalUnitSubquotientFinite` at
line 375.

The original copyright and author header is kept. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` give the Apache-2.0 license
and attribution.
