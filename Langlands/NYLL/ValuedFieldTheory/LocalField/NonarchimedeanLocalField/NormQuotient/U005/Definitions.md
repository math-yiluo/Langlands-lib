# Canonical projection to the general norm quotient

`Langlands.NYLL.LocalFieldTheory.normClass` is the canonical homomorphism
from `Kˣ` to the published named quotient by the image of the norm on units.
Its full telescope is

```lean
normClass.{u} (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Langlands.NYLL.LocalFieldTheory.NormQuotient K L
```

The fields share one arbitrary universe `u`. Both field arguments are explicit;
the two field structures and the algebra structure are instance-implicit.
This is a data definition of a multiplicative homomorphism. No
finite-dimensionality, separability, Galois, local-field, valuation or topology
hypothesis is present.

For `N = localNormSubgroup K L`, the published dependencies define

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

The homomorphism sends `x : Kˣ` to its actual coset `QuotientGroup.mk x`.
The target carries the published `normQuotientCommGroup K L`; its
multiplication and identity are the standard Mathlib quotient-group operations.
Thus multiplication of represented classes is the class of the product.

## Construction and representation boundary

The source body is preserved exactly:

```lean
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N
```

The first step exposes `NormQuotient` as its concrete quotient. The local
abbreviation `N` names the existing subgroup; the last step reuses Mathlib's
canonical quotient homomorphism. In the approved Mathlib,
`Mathlib/GroupTheory/QuotientGroup/Defs.lean` lines 86–101 define
`QuotientGroup.mk' N` using `MonoidHom.mk' QuotientGroup.mk`, with
multiplicativity by reflexivity, and identify its underlying function with
`QuotientGroup.mk`. No replacement quotient or projection is introduced.

`NormQuotient` and `normClass` are ordinary, semireducible definitions.
The named quotient and the concrete quotient are definitionally equal at
Lean's default transparency. The named target's multiplication is the
projection of the published `normQuotientCommGroup`; on the concrete type
Mathlib infers the projection of `QuotientGroup.Quotient.group N`. Their
operations agree definitionally at default transparency. They are different expressions. In particular, `with_reducible rfl` does
not prove equality of the named and concrete types or the projection
application with its quotient class; default-transparency `rfl` does. Neither
ordinary definition is a reducible abbreviation.

Clients needing the concrete quotient API can use the independently published
`normQuotientConcreteEquiv K L`. As the original docstring of that equivalence
instructs, it is the explicit representation boundary. The public evaluation
lemma for this projection is the separate later unit M093.006; this unit
publishes only the projection data.

## General norm convention

The implementation uses Mathlib's unrestricted `Algebra.norm K`, as do the
published `normUnits` and `localNormSubgroup`. The algebra norm is defined
without a finite-module hypothesis. When `L` is not a finite `K`-module,
`Algebra.norm_eq_one_of_not_module_finite` says it is constantly `1`
(`Mathlib/RingTheory/Norm/Defs.lean` lines 59–79). Its image on units is then
the trivial subgroup. The canonical quotient projection still exists.

Adding a finiteness premise would unnecessarily restrict this construction,
change the source telescope and break agreement with the general published
dependencies. Finiteness hypotheses belong to later results that need them.
This definition supplies no Artin map, reciprocity, norm-kernel, finiteness or
continuity theorem.

## Source, adaptation and reuse

This is source unit M093.005 in the published NYLL declaration partition
`notes/reuse/nyll-public-port/m073-m096.md`. The original is Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, retained in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relative source path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`.
Its SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
The entire original file was read. Lines 1–5 carry attribution, line 24
declares `u v`, lines 26–47 define the published subgroup, quotient, group
and representation equivalence, and lines 49–54 define this projection.
Lines 56–63 are the later evaluation theorem and are excluded.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` |

The telescope, docstring and body are unchanged. Worker 107 added the
namespace prefix and this documentation, replaced the source imports with the
published U004 module, omitted the unused universe `v` and all other source
declarations, and retained `noncomputable section`. The published partition
records no patch10 modification to this module. No other worker's draft or
patch10 implementation was reused.

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U004.Definitions`.
Its published chain is U004 → U003 → U002 → U001 → NormUnits/U002 →
`Mathlib.RingTheory.Norm.Transitivity`. This supplies the actual unit norm,
its range, the named quotient and group instance, the representation
equivalence and Mathlib's quotient API. No further import is needed, and no
M092 theorem or later M093 declaration is used.

Fresh task, current Library and approved Mathlib declaration searches found
no existing `normClass` declaration or duplicate task. The related host
`Langlands.LocalClassField.normQuotientProjection` in
`Langlands/ClassFieldTheory/Local/Norms.lean` uses the same canonical Mathlib
projection, but its telescope has independent field universes and a
`FiniteDimensional K L` premise. It therefore does not supply this unrestricted
named NYLL interface. No host declaration is changed or compared by a public
theorem here.

The related registration `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Workspace, project and current Library errata locations were checked for both
registrations; no applicable erratum was found.

## Development checks

The approved Lean service built the definition and a separate private semantic
probe successfully, with zero errors or warnings, in Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Declaration inspection reports
ordinary definition data, the sole universe parameter `u`, and only the
standard assumptions `propext`, `Classical.choice` and `Quot.sound`.

The complete unapplied constant was inspected. The probe checks five binders:
explicit `K`, explicit `L`, and the three instance-implicit structures. Its
result is `MonoidHom` with the named target. The target `MulOne` argument is
syntactically the inferred projection of `normQuotientCommGroup K L`.
Reflexivity checks the exact canonical homomorphism, its underlying
`QuotientGroup.mk` function after exposing `NormQuotient`, agreement of named
and concrete multiplication, the class of a product, and the actual
`Units.map (Algebra.norm K)` image. The transparency checks described above
also succeed. These private development checks are excluded from the public
candidate; they support independent review and are not acceptance evidence or
additional public theorem units.

## Attribution

The original 2026 Naganori Yamaguchi copyright and author header is retained
verbatim, including “Naganori Yamaguchi (assisted by OpenAI Codex)”. The
source is Apache-2.0. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained through the
submission's `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
both byte-identical to the retained original. The source NOTICE has no
NormQuotient-specific third-party entry. Worker 107 performed this extraction;
no other project worker contributed code or a reused draft to this unit.
