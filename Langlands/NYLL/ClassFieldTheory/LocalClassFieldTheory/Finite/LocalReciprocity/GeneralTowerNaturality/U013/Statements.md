# Restriction along an algebra equivalence is conjugation: statement target

`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongrStatement`
covers a `K`-algebra equivalence `e : L ≃ₐ[K] M` with `M` normal over `K`.
Make `L` an `M`-algebra through `e.symm`. The proposition says that Mathlib's
restriction `Gal(L/K) →* Gal(M/K)` then equals conjugation by `e`. In Lean:

```lean
def restrictNormalHom_eq_autCongrStatement
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) : Prop :=
    letI : Algebra M L := e.symm.toRingHom.toAlgebra
    letI : IsScalarTower K M L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (e.symm.commutes x).symm)
    (AlgEquiv.restrictNormalHom M :
        Gal(L / K) →* Gal(M / K)) =
      (AlgEquiv.autCongr e).toMonoidHom
```

This is the statement of source unit M262.013. Defining the proposition does not
prove it.

## Parameters and meaning

All three fields lie in `Type 0`, as in the source, and the declaration has no
universe parameters. The parameters are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K`, `L`, `M` | explicit, `Type` | Base field and two extensions |
| `[Field K]`, `[Field L]`, `[Field M]` | instance-implicit | Field structures |
| `[Algebra K L]`, `[Algebra K M]` | instance-implicit | The two given `K`-algebra structures |
| `[Normal K M]` | instance-implicit | Normality of `M / K`, needed by `restrictNormalHom` |
| `e : L ≃ₐ[K] M` | explicit | The `K`-algebra equivalence |

No `M`-algebra structure on `L` is assumed. The statement constructs one
locally, together with the scalar-tower instance that the restriction needs:

- `Algebra M L` is `e.symm.toRingHom.toAlgebra`, so `m : M` acts on `L` through
  `e.symm m`.
- `IsScalarTower K M L` comes from `IsScalarTower.of_algebraMap_eq'`. The proof
  term checks, pointwise by `e.symm.commutes`, that `algebraMap K L` equals
  `algebraMap M L` composed with `algebraMap K M`.

Both are `letI` bindings inside the proposition, exactly as in the source
statement. The instance proof is a proof term, so the proposition does not
depend on how it is proved.

The two sides of the equation are Mathlib's monoid homomorphisms
`Gal(L/K) →* Gal(M/K)`:

- `AlgEquiv.restrictNormalHom M` (`Mathlib/FieldTheory/Normal/Defs.lean`, lines
  194–196) is restriction to the normal subextension `M` of `L / K`, under the
  local instances above.
- `AlgEquiv.autCongr e` (`Mathlib/Algebra/Algebra/Equiv.lean`, line 677) sends
  `ψ` to `e.symm.trans (ψ.trans e)`, that is, `e ∘ ψ ∘ e⁻¹`. Its
  `toMonoidHom` forgets that it is an isomorphism.

So the proposition asserts that, for every `sigma : Gal(L/K)`, the restriction
of `sigma` to `M` through `e.symm` is `e ∘ sigma ∘ e⁻¹`. It is an equality of
monoid homomorphisms. The statement assumes no finite-dimensionality, Galois,
valuation, topology or local-field hypothesis.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`.
The relevant lines are:

- the docstring at lines 402–404;
- the theorem's telescope and statement at lines 405–419;
- the proof at lines 419–436.

The file's SHA-256 is
`a81fa466df15d0d72f24428f0780a68b9a9f434fa4d27746beafe71bfae521c0`. The
source file declares no `variable` before this theorem, so its binders are the
whole telescope. The source statement is:

```lean
theorem restrictNormalHom_eq_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) :
    letI : Algebra M L := e.symm.toRingHom.toAlgebra
    letI : IsScalarTower K M L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (e.symm.commutes x).symm)
    (AlgEquiv.restrictNormalHom M :
        Gal(L / K) →* Gal(M / K)) =
      (AlgEquiv.autCongr e).toMonoidHom := by
```

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.restrictNormalHom_eq_autCongr` (M262.013) | `Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongrStatement` |

Row M262.013 of the published partition
[`notes/reuse/nyll-public-port/m259-m262.md`](../../../../../../../../notes/reuse/nyll-public-port/m259-m262.md)
reserves `Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongr`
for the later proof. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
gives the `Statement` suffix for the target. The partition's predecessor
`M262.012.END` is scheduling order only: the statement mentions no earlier
source declaration. No NYLL erratum for this module was found in the current
Library's `notes/`.

## Imports and modification record

The only direct import is `Mathlib.FieldTheory.Normal.Defs`. It defines `Normal`
and `AlgEquiv.restrictNormalHom` and, through its own imports, supplies
`AlgEquiv.autCongr`, `IsScalarTower.of_algebraMap_eq'` and the `Gal(L / K)`
notation. Every transitive import lies in the approved Mathlib environment. No
external NYLL module is imported. The source's broad imports are not needed and
are dropped.

The adaptation makes three changes:

- it moves the theorem's telescope and its complete statement into the
  Prop-valued definition above. The statement includes both `letI` bindings
  with their proof term. Binder order, binder kinds, binder names, local
  instances, type ascription and conclusion are unchanged;
- it omits the source proof and every other declaration of the module;
- it puts the definition in the namespace `Langlands.NYLL.LocalClassFieldTheory`
  and keeps the source's `noncomputable section`.

The source docstring is retained. The Lean header records these changes with
Worker 30's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
whose type ends in `Prop` (`statement_returns_prop: true`), with no level
parameters and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. This development check is not independent acceptance.

## Boundary and license

This file defines the proposition only. The theorem
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongr` and its
proof need a separate proof task once this target is in the Library. The source
proof checks the equation pointwise. It applies `e.symm.injective` and uses
`AlgEquiv.restrictNormal_commutes` together with `AlgEquiv.autCongr_apply`.
The later M262.014 unit, `abelianLocalArtinMonoidHom_autCongr`, is separate
and depends on the abelian local Artin map, which is not yet in the Library.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 30
adapted this unit directly from the pinned original; no other project worker
supplied code.
