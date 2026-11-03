# Equal norm classes and unit-norm ratios

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassEqIffExistsNormDivStatement.{u}`
by the single theorem
`Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_exists_norm_div`.
Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U031.Statements`.
The statement pair and the entire published import chain remain unchanged.

## Exact target and mathematical meaning

The unapplied theorem type is exactly
`NormClassEqIffExistsNormDivStatement.{u}`. There are no external term
or instance parameters. Unfolding that proposition gives

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
  normClass K L x = normClass K L y ↔
    ∃ z : Lˣ, x / y = normUnits K L z
```

All seven original binders remain internal, in source order:
the explicit types `K` and `L`, the instance-implicit structures
`[Field K]`, `[Field L]`, `[Algebra K L]`, and the explicit base-field
units `x` and `y`. The fields share one arbitrary universe `u`.
There is no finite-dimensionality, finite-module, local-field,
separability, Galois, valuation or topology premise.

Here the existing public `normUnits K L : Lˣ →* Kˣ` is
`Units.map (Algebra.norm K)`. Its range is exactly the existing
`localNormSubgroup K L`, and the existing `NormQuotient K L` is
`Kˣ ⧸ localNormSubgroup K L`, with the published commutative group
structure. The existing `normClass K L` is the canonical quotient
homomorphism `QuotientGroup.mk' (localNormSubgroup K L)`.
The left side therefore compares classes in the actual quotient by
the actual norm image. The ratio `x / y` is division in `Kˣ`,
and the witness `z` is a unit of `L`. The witness equation places
`x / y` on the left and `normUnits K L z` on the right.
Both implications hold for the unrestricted published algebra norm.
These meanings come from the unchanged public constructions in
`NormUnits.U002.Definitions` and `NormQuotient.U001`, `U002`, `U003`
and `U005`.

## Implemented proof

The proof introduces the seven binders with
`intro K L _ _ _ x y`. It then follows the original proof:

1. Rewrite by the public
   `normClass_eq_iff_div_mem K L x y` from U019.Proofs, inherited
   through U031.Statements. Equality of norm classes becomes
   `x / y ∈ localNormSubgroup K L`.
2. Use the definition of that subgroup to change this membership
   to `x / y ∈ (normUnits K L).range`.
3. Rewrite with Mathlib's `MonoidHom.mem_range`, obtaining
   `∃ z : Lˣ, normUnits K L z = x / y` on the left.
4. In each direction, retain the same unit witness `z` and reverse
   its equation with `hz.symm`.

The result has exactly the requested witness and equation orientation.
The proof adds no helper declaration, construction, instance or simp
registration. It uses the published membership criterion rather than
reproving the quotient criterion.

## Original and declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:274–286`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L274-L286):
docstring 274, theorem and telescope 275–276, conclusion 277–278,
and proof 279–286. The complete original file was read; its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Its norm subgroup, quotient, group structure and class map occur at
26–54, and its reused membership criterion at 183–190.
The complete original `Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`
was also read; its SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`,
and its `normUnits` definition is at 32–34.
The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
identifies this unit as M093.031.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_eq_iff_exists_norm_div` | Existing closed `NormClassEqIffExistsNormDivStatement.{u}` in U031.Statements |
| Truth proof of `normClass_eq_iff_exists_norm_div` | `normClass_eq_iff_exists_norm_div`, proved here with that exact closed type |
| `normClass_eq_iff_div_mem` | Existing U019.Proofs theorem, reused unchanged |
| `normUnits`, `localNormSubgroup`, `NormQuotient`, `normQuotientCommGroup`, `normClass` | Existing public constructions, unchanged |

Worker 1153 adapted the pinned original directly on 3 November 2026.
The namespace gains `Langlands.NYLL`, and the proof introduces the
binders now internal to the independently published proposition before
using the original proof body. Only U031.Statements is directly
imported. The original noncomputable section, unused universe `v`
and unrelated declarations are omitted. M093 has no patch10 change;
no feasibility patch or unpublished shared proof draft was reused.
Worker 248's independently published statement is an unchanged
dependency, not a reused proof draft.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The six `notes/errata/<source id>.md` paths for these source IDs in the
workspace, project and supplied Library were checked; none exists.
The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and scope

The original copyright and author header is retained verbatim,
including “Naganori Yamaguchi (assisted by OpenAI Codex)”, followed
by the dated modification record. Worker 1153 is the sole project
proof contributor. Existing dependency attributions remain unchanged.
The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained through
`repository_paths`, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

M093.032 onward and host adapters remain separate work. Parent
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the named Artin-map
family for every prime and arbitrary supplied `TF` and `TE`, its actual
norm image and exact norm kernel, host quotient and evaluation,
bijectivity, actual quotient and finite discrete Galois topologies,
and both continuity directions. Type 0 does not discharge universe
transport. This generic support lemma supplies no normalization,
inertia, cohomological comparison or reciprocity theorem.
Independent semantic acceptance, Lake/kernel/exact-target and
frozen-dependency validation, and Integrator publication remain
separate requirements.
