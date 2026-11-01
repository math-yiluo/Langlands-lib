# Inclusion-induced norm quotient maps on representatives

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.NormQuotientMapOfLENormClassStatement.{u}`
as the exact theorem
`Langlands.NYLL.LocalFieldTheory.normQuotientMapOfLE_normClass`.
It is the proof phase of M093.024 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093).
Its sole direct import is the public U024 Statements module.

## Exact target and mathematical scope

The theorem has no external term or instance parameters. Its complete
unapplied type is `NormQuotientMapOfLENormClassStatement.{u}`, whose
already published body is:

```lean
∀ (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  (h : localNormSubgroup K L ≤ localNormSubgroup K M) (x : Kˣ),
  normQuotientMapOfLE K L M h (normClass K L x) = normClass K M x
```

All ten binders occur inside this closed proposition, in the displayed
order and with the displayed binder kinds. The three fields share the
sole arbitrary universe `u`. No finite-dimensionality, scalar tower,
`Algebra L M`, local-field or topology hypothesis is present.
The [statement companion](Statements.md) explains the complete interface.
The statement pair and all imported Lean/Markdown pairs are unchanged.

The public definitions use the actual unit norm
`normUnits K L = Units.map (Algebra.norm K)`, its range
`localNormSubgroup K L`, and the quotient
`NormQuotient K L = Kˣ ⧸ localNormSubgroup K L`.
`normClass K L` is the canonical quotient homomorphism.
The hypothesis includes the source norm image in the target norm image.
The named `normQuotientMapOfLE K L M h` therefore descends
`normClass K M` through the quotient by `localNormSubgroup K L`.
The conclusion evaluates this very map on the canonical class of the
same representative `x : Kˣ`.

The proof retains Mathlib's unrestricted `Algebra.norm` convention.
At the approved Mathlib pin,
`Mathlib/RingTheory/Norm/Defs.lean:59–62` defines this norm by the
determinant of multiplication, and
`Algebra.norm_eq_one_of_not_module_finite` at lines 76–79 makes it
constantly `1` when the module is not finite. The unit norm then has
trivial image. This convention applies separately to both extensions;
the proof neither strengthens the assumptions nor treats that case as
an omitted exception.

## Implemented proof

The entire proof body is:

```lean
  intro K L M _ _ _ _ _ h x
  exact normQuotientLift_normClass (normClass K M) _ x
```

The introduction exposes the three field types, three field structures,
two algebra structures, subgroup inclusion and unit representative.
The existing definition of `normQuotientMapOfLE` is

```lean
normQuotientLift (normClass K M) fun y hy =>
  (normClass_eq_one_iff_mem K M y).2 (h hy)
```

Thus definitional reduction identifies the goal with the representative
equation for `normQuotientLift`, specialized to the target group
`NormQuotient K M` and homomorphism `normClass K M`. The underscore
in the final application is inferred as the displayed proof that every
source norm is in the kernel of that homomorphism. The public
`normQuotientLift_normClass` from U008.Proofs supplies the equation.
Its published implementation applies Mathlib's
`QuotientGroup.lift_mk`; this module reuses that theorem by Lean name.
No new data, instance, statement, helper theorem or simp registration
is introduced.

## Pinned original and theorem map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:222–229`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L222-L229):
docstring at line 222, simp attribute at 223, theorem name, telescope and
result at 224–228, and proof at 229. The complete original file was read;
its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The map being evaluated is at lines 213–220, and the general lift and
its representative theorem are at lines 65–81.
The original unit norm is in
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:32–34`, whole-file
SHA-256 `1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| `normQuotientMapOfLE_normClass` | This theorem of the published closed `NormQuotientMapOfLENormClassStatement` |
| `normQuotientMapOfLE` | Public U023.Definitions construction, unchanged |
| `normQuotientLift_normClass` | Public U008.Proofs theorem, reused |
| `normQuotientLift`, `normClass`, `localNormSubgroup`, `NormQuotient`, `normUnits` | Existing public constructions, unchanged |

Worker 107's adaptation on 1 November 2026 preserves the original final
proof application. It adds the namespace prefix and introductions for
the binders packaged by the published closed statement, uses the sole
U024 Statements import and sole shared universe `u`, and omits the source
simp attribute, noncomputable section, unused `v` and unrelated declarations.
M093 has no feasibility patch10 modification. No shared proof draft
or other worker's unpublished work was reused.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both source-ID errata paths were checked in the workspace, project and
supplied Library; none exists.

The approved environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Attribution and remaining obligations

The original 2026 Naganori Yamaguchi copyright and author header is
retained verbatim, including “Naganori Yamaguchi (assisted by OpenAI
Codex)”, with an explicit dated modification record. Worker 107 adapted
this proof directly from the pinned original and wrote this companion.
There are no other project coauthors or reused-draft contributors.
Published dependency authors and notices remain unchanged.
The inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained unchanged
through `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
They match the originals, including all inherited dependency notices.

This generic algebraic representative equation does not supply the host
named Artin family, its actual norm-kernel theorem, a reciprocity quotient
equivalence, host evaluation or continuity. Parent task
`1cbd1968-d285-4b34-822c-f6b5599d1c38` retains the every-prime,
arbitrary supplied topology, actual norm-image and named-map obligations.
The existing cohomological definitions and frozen proof targets retain
their meaning. M093.025, later source units and host adapters remain
outside this module. Development compilation establishes neither
independent semantic acceptance nor Integrator publication.
