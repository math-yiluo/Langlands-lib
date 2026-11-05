# Left multiplication by an integer power of a unit norm

The sole new declaration is the closed proposition
`Langlands.NYLL.LocalFieldTheory.NormClassNormUnitsZpowMulStatement.{u} : Prop`.
It packages the asserted type of NYLL unit M093.034,
`LocalFieldTheory.normClass_normUnits_zpow_mul`. This is its statement
phase; the module supplies no truth proof. Its sole direct import is the
published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U033.Proofs`,
whose complete published dependency chain is preserved unchanged.

## Full telescope and conclusion

The entire definition body is

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (z : Lˣ) (n : Int) (x : Kˣ),
  normClass K L ((normUnits K L z) ^ n * x) = normClass K L x
```

There is one arbitrary shared universe `u`, and no external term or
instance parameter. All eight binders occur inside the proposition in
their original order:

| Position | Binder | Kind and role |
| --- | --- | --- |
| 1 | `K : Type u` | Explicit base-field type |
| 2 | `L : Type u` | Explicit extension-field type |
| 3 | `[Field K]` | Instance-implicit field structure on `K` |
| 4 | `[Field L]` | Instance-implicit field structure on `L` |
| 5 | `[Algebra K L]` | Instance-implicit algebra structure |
| 6 | `(z : Lˣ)` | Explicit extension-field unit |
| 7 | `(n : Int)` | Explicit integer exponent |
| 8 | `(x : Kˣ)` | Explicit base-field unit |

There is no finite-dimensionality, finite-module, valuation, topology,
local-field, separability or Galois premise. The assertion concerns any
two fields with the indicated algebra structure in the shared universe.

The expression `(normUnits K L z) ^ n` is an integer power in the
unit group `Kˣ`. It includes negative exponents, interpreted using the
inverse unit, and exponent zero, whose power is `1`. The type of `n`
is `Int` throughout. This power multiplies `x` on the left in `Kˣ`;
the full product is formed before applying `normClass K L`. The
asserted equality compares the resulting quotient class with the class
of `x`. The right-multiplication statement M093.035 is separate work.

## Concrete norm, image and projection

All constructions are the existing public declarations in
`Langlands.NYLL.LocalFieldTheory`:

| Declaration | Existing module | Meaning |
| --- | --- | --- |
| `normUnits` | `LocalField.NormUnits.U002.Definitions` | `Units.map (Algebra.norm K) : Lˣ →* Kˣ` |
| `localNormSubgroup` | `NormQuotient.U001.Definitions` | `(normUnits K L).range` |
| `NormQuotient` | `NormQuotient.U002.Definitions` | `Kˣ ⧸ localNormSubgroup K L` |
| `normQuotientCommGroup` | `NormQuotient.U003.Definitions` | The quotient commutative-group structure |
| `normClass` | `NormQuotient.U005.Definitions` | The canonical homomorphism `QuotientGroup.mk' (localNormSubgroup K L)` |

The module prefixes in this table abbreviate
`Langlands.NYLL.ValuedFieldTheory.` and its
`LocalField.NonarchimedeanLocalField.` subtree as appropriate.
The subgroup is the actual range of the algebra norm on units, and
`normClass` is the actual quotient projection. None is replaced or
redefined in this unit. The support `normUnits` allows independent field
universes; this assertion uses its shared-universe specialization.
The host `Langlands.LocalClassField.NormQuotient`, which has a
finite-dimensionality parameter, does not replace this generic support
interface.

## Source pin and adaptation

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:302–308`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean#L302-L308):
the docstring is at 302, theorem name and type binders at 303, structures,
extension unit, integer and base unit at 304, conclusion at 305–306,
and proof at 307–308. The original asserted type is

```lean
theorem normClass_normUnits_zpow_mul (K L : Type u)
    [Field K] [Field L] [Algebra K L] (z : Lˣ) (n : Int) (x : Kˣ) :
    normClass K L ((normUnits K L z) ^ n * x) =
      normClass K L x
```

Worker 1560 read the complete retained original file on 5 November 2026
UTC. Its whole-file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The original subgroup, quotient, group structure and projection are at
26–54, and the integer-power class identity is at 268–272.
The complete original
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean` was also read:
its unit norm is defined at 32–34 and its whole-file SHA-256 is
`1960b4f3997936e607090aa565713a378b9c435fb3c29b4bb608514da2d031e9`.
The [public partition](../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m093)
places M093.034 after M093.033, with separate statement and proof
phases. No patch10 compatibility edit applies to M093.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `normClass_normUnits_zpow_mul` | Closed `NormClassNormUnitsZpowMulStatement.{u}` in this module |
| `normUnits`, `localNormSubgroup` | Existing public unit norm and its range, unchanged |
| `NormQuotient`, `normQuotientCommGroup`, `normClass` | Existing public quotient, group structure and canonical projection, unchanged |
| `normClass_normUnits_zpow_eq_one` | Existing public U030.Proofs theorem, inherited through U033 |
| Truth proof of `normClass_normUnits_zpow_mul` | Deferred exact theorem with the adapted original name |

This extraction adds the `Langlands.NYLL` namespace prefix and moves
the eight source binders into a Prop-valued definition without
changing their order or binder kinds. The original docstring is
retained. The sole U033.Proofs import replaces the original import
list while retaining the public chain. The unused universe `v`,
noncomputable section, proof body and unrelated declarations are
omitted. The definition needs no noncomputable section, instance or
simp registration. Worker 1560 authored this extraction and companion
directly from the pinned source; no unpublished project draft was
reused and there are no project coauthors for this pair.

The retained source belongs to registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Both registrations' `notes/errata/<source id>.md` paths were checked
in the workspace, project and supplied Library; all six were absent
on 5 November 2026 UTC.

## Deferred proof and scope

After independent statement acceptance and publication, the separate
proof phase can prove
`Langlands.NYLL.LocalFieldTheory.normClass_normUnits_zpow_mul` with
exact closed type `NormClassNormUnitsZpowMulStatement.{u}`. The original
proof uses `map_mul`, then
`normClass_normUnits_zpow_eq_one K L z n` to replace the class of the
integer power by `1`, and finally `one_mul`. The existing public
U030.Proofs supplies the integer-power identity through the unchanged
U033 chain. This describes the original proof route; the present
module supplies only the proposition definition.

M093.035 onward and all host adapters remain separate work. Parent
task `1cbd1968-d285-4b34-822c-f6b5599d1c38` retains its named Artin-map
family, actual norm kernel and quotient, evaluation, bijectivity and
continuity obligations for all primes and arbitrary supplied `TF`
and `TE`. The actual quotient topology, finite discrete Galois
topology and both continuity directions require their own results.
Type 0 is only the initial host stage. This generic assertion
establishes no reciprocity, normalization, inertia, universe transport
or comparison with the cohomological route. Existing cohomological
definitions and frozen targets retain their meanings.

## License and environment

The Lean file retains the original 2026 Naganori Yamaguchi copyright
and author header verbatim, including “Naganori Yamaguchi (assisted
by OpenAI Codex)”, followed by a dated modification record. The
inherited Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE), including
inherited dependency attribution, are retained unchanged in
`repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Compilation and proposition inspection are development checks;
independent semantic acceptance and Integrator publication remain
necessary under `lean.statement@1`.
