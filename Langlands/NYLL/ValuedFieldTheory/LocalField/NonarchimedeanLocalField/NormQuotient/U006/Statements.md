# Concrete evaluation of a norm class

`Langlands.NYLL.LocalFieldTheory.NormQuotientConcreteEquivNormClassStatement.{u}`
is the following closed proposition:

```lean
∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
  Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv K L
      (Langlands.NYLL.LocalFieldTheory.normClass K L x) =
    QuotientGroup.mk x
```

The declaration itself has type `Prop` and no term parameters. Its sole
universe parameter is `u`. Both fields, their two field structures, their
algebra structure and the unit `x` are quantified inside the proposition.
There is no finite-dimensionality, separability, Galois, local-field,
valuation, topology or additional proof premise. This artifact defines the
target proposition; it does not prove the equation.

## Meaning of the equation

The only direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions`.
Its chain U005 → U004 → U003 → U002 → U001 → NormUnits/U002 supplies
the following existing constructions:

```lean
normUnits K L = Units.map (Algebra.norm K)
localNormSubgroup K L = (normUnits K L).range
NormQuotient K L = Kˣ ⧸ localNormSubgroup K L
```

Thus the subgroup consists of actual norms of units of `L`. The named
quotient carries the published `normQuotientCommGroup K L`, obtained from
Mathlib's commutative quotient-group structure.

The published multiplicative equivalence
`normQuotientConcreteEquiv K L` goes from `NormQuotient K L` to the actual
concrete quotient `Kˣ ⧸ localNormSubgroup K L`. Its body exposes the named
quotient and returns `MulEquiv.refl _`. Its underlying function is therefore
the identity after exposing that representation.

The published homomorphism `normClass K L` exposes the same quotient, names
the existing subgroup `N`, and returns `QuotientGroup.mk' N`.
In the approved Mathlib, `Mathlib/GroupTheory/QuotientGroup/Defs.lean`
lines 86–101 define that homomorphism using `MonoidHom.mk' QuotientGroup.mk`
and identify its underlying function with the quotient class constructor.
Consequently both sides of the target equation are elements of the concrete
quotient by `localNormSubgroup K L`; the right side uses Mathlib's existing
`QuotientGroup.mk`. This statement introduces no new projection, subgroup,
quotient or equivalence.

`NormQuotient`, `normQuotientConcreteEquiv` and `normClass` are ordinary
semireducible definitions. Exposing their bodies uses Lean's default
transparency; they are not reducible abbreviations. The named group operations
agree definitionally at default transparency with the concrete quotient
operations. The equivalence is the published representation boundary for
clients needing the concrete quotient API. The present declaration is also
an ordinary definition, whose value is the universally quantified proposition.

## General norm convention

The dependencies retain Mathlib's unrestricted `Algebra.norm K`, which is
defined without a finite-module hypothesis. In
`Mathlib/RingTheory/Norm/Defs.lean` lines 59–79,
`Algebra.norm_eq_one_of_not_module_finite` states that the norm is constantly
`1` when `L` is not a finite `K`-module. Its image on units is then trivial.
The quotient, projection and representation equivalence still have their
stated meanings, so no finiteness premise is added to this representation
equation.

## Source and adaptation

This is the statement phase of source unit M093.006, identified in the
published partition `notes/reuse/nyll-public-port/m073-m096.md`.
The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, retained in the registered
source `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its relative path is
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`;
the file SHA-256 is
`26137f1ab7816fc2c6a05b60a10f66275305c17cecbb6b71b05d093ad1140a0f`.
Original lines 1–100 were read independently for this task: lines 1–5 give
attribution, lines 26–54 give the published prerequisites, and lines 56–63
give the source evaluation theorem.

| Original declaration | Adapted statement |
| --- | --- |
| `LocalFieldTheory.normQuotientConcreteEquiv_normClass` | `Langlands.NYLL.LocalFieldTheory.NormQuotientConcreteEquivNormClassStatement` |

Worker 107 preserved the original equality and shared arbitrary universe,
added the namespace prefix, and moved every term binder from the theorem
telescope into universal quantification inside `Prop`. The source proof and
`@[simp]` registration are omitted. The unused universe `v`, source-wide
imports, `noncomputable section` and all other source declarations are omitted;
the single published U005 import supplies everything needed. There is no
computational definition requiring a noncomputable section in this unit.
The original theorem name
`Langlands.NYLL.LocalFieldTheory.normQuotientConcreteEquiv_normClass`
is reserved for a separate later exact proof.

The partition records no patch10 change to this module. The related source
registration `nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Workspace, project and current Library errata locations were checked for
both registrations; no applicable erratum was found.

Current Library, approved Mathlib and task searches found no existing target
or duplicate evaluation task beyond this task and predecessor scope
references. Mathlib's quotient projection supplies the existing coset map.
The host `Langlands.LocalClassField.normQuotientProjection` has independent
field universes and a `FiniteDimensional` premise and does not supply this
named NYLL representation equation.

This unit provides no later quotient construction, host adapter, Artin map,
norm-kernel, reciprocity or continuity result. Publication of the target
leaves its separate proof obligation and parent finite reciprocity work open.

## Development checks

The approved Lean service compiled the dependency-first module list ending in
this Statements module in Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with zero errors or warnings.
Inspection of the exact declaration reports an ordinary definition, sole
universe parameter `u`, and `statement_returns_prop: true`. The complete
unapplied type is `Prop`; a private printed-declaration check confirms that
all six term binders are inside its value and that the equation uses the
published equivalence and projection in the same universe. The only recorded
assumptions are `propext`, `Classical.choice` and `Quot.sound`.
These are development compilation and inspection checks, not a proof of
the proposition or independent semantic acceptance. The private check module
is excluded from the public candidate.

## Attribution

The original copyright and author header is retained verbatim, including
“Naganori Yamaguchi (assisted by OpenAI Codex)”. The source is Apache-2.0.
The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained through
the submission's `repository_paths`. Their respective SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
both byte-identical to the retained originals. The source NOTICE has no
NormQuotient-specific third-party entry. Worker 107 performed this adaptation;
no other project worker's draft was reused.
