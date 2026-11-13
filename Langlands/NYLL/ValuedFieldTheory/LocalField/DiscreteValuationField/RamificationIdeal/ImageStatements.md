# M344.002–004: maximal-ideal image and power targets

The paired Lean module extracts three theorem conclusions from Naganori
Yamaguchi's NYLL, commit `fbd320cd8b1b06487c58227e92eb135794267709`.
It defines propositions; it supplies no proofs of them.

The original file is
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationIdeal.lean`.
Its SHA-256 is
`e40eebb2c83766ee7949ffceefcfbab5f4f3cb8d1ee4908340f8c5d7f49a8850`.
It is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The original copyright, license and author header is retained; the carried
license and notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 308 supplied the initial focused design, and Worker 228 prepared this
paired extraction for publication.

All original names in the table are in
`LocalFieldTheory.DiscreteValuationField.ValuedExtension`; all adapted names
are in `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension`.
The table gives the complete original-to-adapted declaration correspondence.

| Source unit | Source type lines | Source name | Adapted name |
| --- | --- | --- | --- |
| M344.002 | 50–52; proof 53–73 | `maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex` | `maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndexStatement` |
| M344.003 | 77–80; proof 81–88 | `maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndex` | `maximalIdeal_pow_map_eq_target_maximalIdeal_pow_mul_ramificationIndexStatement` |
| M344.004 | 91–95; proof 96–98 | `integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex` | `integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndexStatement` |

The common source context, lines 21–32, has four independent universes
`u v w x`, implicit fields `{K : Type u}` and `{L : Type w}`, instances
`[Field K] [Field L] [Algebra K L]`, explicit chosen packages
`(base : CompleteDVF.{u, v} K)` and `(target : CompleteDVF.{w, x} L)`,
and `[base.valuation.HasExtension target.valuation]`. Every target retains
this context and its binder order. The complete packages and their canonical
valuation-subring and maximal-ideal projections are imported from the
published `Complete.Projections` module.

The first target states that the base maximal ideal maps to the target
maximal ideal raised to the ramification index. The second retains the
explicit `(n : ℕ)` argument and maps the `n`-th power to exponent `e * n`,
in that order. The third retains implicit `{n : ℕ}` and
`{x : base.valuationSubring}` followed by explicit
`(hx : x ∈ base.maximalIdeal ^ n)`, and states membership of the mapped
element in that same target power. The explicit proof argument belongs to
the definition's outer telescope, although its value is unused in the body.
The unused-variable linter is disabled only for that declaration.
No finite-dimensionality or module torsion-freeness instance is added.

Two source wrappers are inlined using their definitionally identical
Mathlib bodies. In
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean`
at the same commit (SHA-256
`e8999a99fc7ff6c38bd68742b9c7779decfbb2d042f60779bd2386d7950232b5`),
M108.003, lines 53–56, defines
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex`;
M108.005, lines 65–67, defines
`ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap`.
Their occurrences are replaced as follows:

| Source expression | Expression used in the paired Lean |
| --- | --- |
| `ramificationIndex base.toDVF target.toDVF` | `Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` |
| `integerMap base.toDVF target.toDVF` | `algebraMap base.valuationSubring target.valuationSubring` |

The `CompleteDVF.toDVF` projection preserves the actual valuation subrings
and maximal ideals definitionally. Mathlib's `Valuation.HasExtension`
supplies the canonical algebra between those subrings. Thus the substitutions
preserve the source conclusions without new definitions or global instances.

The modifications are extraction of these three units; the namespace prefix;
the `Statement` suffix and replacement of each theorem and proof by a
`def` returning `Prop` with the original conclusion as its body; the two
definitional substitutions above; replacement of the original
`RamificationInvariants` import by the two Mathlib imports and the published
`Complete.Projections` import; formatting and descriptive docstrings; and
the scoped linter setting retaining `hx`. No other source units are claimed.
Exact proof successors are separate work after these targets are published.
