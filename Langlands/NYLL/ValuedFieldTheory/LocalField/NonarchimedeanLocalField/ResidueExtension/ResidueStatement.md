# Reduction commutes with the residue-field algebra map

The Prop-valued definition
`Langlands.NYLL.LocalFieldTheory.residueField_algebraMap_residueStatement`
records the exact statement of NYLL M138.007. For each integer `x` in the
base valuation ring, extending its residue equals reducing its extension.
This contribution publishes the target proposition; it supplies no proof
of that target.

## Pinned source and name map

Naganori Yamaguchi,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`,
lines 88–96](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L88-L96),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`.
The docstring is on line 88, the simp attribute on line 89, the theorem
declaration on lines 90–95, and its proof on line 96.

The original
`LocalFieldTheory.residueField_algebraMap_residue` becomes
`Langlands.NYLL.LocalFieldTheory.residueField_algebraMap_residueStatement`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its readable checkout is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The public inventory is `notes/reuse/nyll-public-port/m121-m144.md`,
M138.007. Source lines 1–100 were read.

## Exact telescope and proposition

There is one source universe `u`. Every binder retains its source kind and
order:

```lean
(K L : Type u)
[Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
(x : 𝒪[K])
```

The definition returns `Prop` with body exactly the source equality:

```lean
algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
  IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)
```

Here `𝒪[K]` and `𝒪[L]` are the actual integer subrings of the supplied
`ValuativeRel` valuations. `𝓀[K]` and `𝓀[L]` are their actual local-ring
residue fields, and `IsLocalRing.residue` is the quotient map. The integer
algebra map is Mathlib's restriction of the supplied `algebraMap K L`;
the residue algebra map is the induced local-ring residue-field map.
Both are the canonical instances already supplied by Mathlib for
`Valuation.HasExtension`. No arbitrary comparison map is introduced.

The theorem needs no local-field topology, finite-dimensionality,
separability or integral-closure assumption. The explicit integer `x`
remains an outer parameter, as in the original theorem.

## Modifications and reuse

Worker 252, 13 November 2026:

- prefixed the namespace with `Langlands.NYLL` and appended `Statement`;
- changed the theorem into a `def` returning `Prop`, retaining the original
  universe, complete telescope, docstring and equation;
- omitted the source `rfl` proof and `@[simp]`, since this unit is a target
  definition;
- extracted only M138.007, replacing the original module documentation;
- replaced the broad original imports, including NYLL `ResidueUnits`,
  with `Mathlib.RingTheory.Valuation.Extension` and
  `Mathlib.Topology.Algebra.Valued.ValuativeRel`.

Mathlib already has the corresponding compatibility theorem
`Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap`
and the general `IsLocalRing.ResidueField.algebraMap_residue`.
These locate a possible later proof route. This candidate keeps the required
named target rather than claiming a proof publication. It needs none of the
preceding NYLL integer-ring or residue-field map aliases and installs no
instances or simp lemmas.

## License

The original copyright and author header remains. The upstream Apache-2.0
license and notice are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
compiled this module with zero errors and warnings and inspected the named
definition with `statement_returns_prop: true`, level parameters `[u]`, and
only `propext`, `Classical.choice` and `Quot.sound`. This development check
does not establish independent acceptance, publication or a target proof.
