# Residue-field algebra automorphisms from an integral-closure restriction

This module adapts NYLL source units M160.005 and M160.006. It exports two
data definitions in the namespace `Langlands.NYLL.LocalFieldTheory`:

- `galoisGroupResidueAlgEquivOfIsIntegralClosure` (M160.005) packages the
  published residue-field equivalence
  `galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ` as an algebra
  automorphism over the base residue field `𝓀[K]`;
- `galoisGroupResidueAlgEquivHomOfIsIntegralClosure` (M160.006) assembles
  these algebra automorphisms into a group homomorphism from `Gal(L/K)`.

The underlying maps are exactly the published ones. The only new
mathematical content is in the two group-law fields of the homomorphism.
They are proved inside the definition from published theorems. Nothing
else is exported.

## Interface and meaning

Both definitions take the complete shared interface

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
[Algebra K L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

The first then takes `σ : Gal(L/K)`. The complete types are:

| Definition in `Langlands.NYLL.LocalFieldTheory` | Further argument | Result type |
| --- | --- | --- |
| `galoisGroupResidueAlgEquivOfIsIntegralClosure.{u}` | `σ : Gal(L/K)` | `𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]` |
| `galoisGroupResidueAlgEquivHomOfIsIntegralClosure.{u}` | none | `Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` |

The universe `u` is arbitrary and shared by `K` and `L`; it is the only
universe parameter of either definition. `Gal(L/K)` is the group
`L ≃ₐ[K] L` of `K`-algebra automorphisms of `L`. It does not assume that
`L/K` is Galois. The scoped integer ring `𝒪[F]` is the actual subtype
`Valuation.integer (ValuativeRel.valuation F)`. The scoped residue field
`𝓀[F]` is `IsLocalRing.ResidueField 𝒪[F]`, the quotient of that integer
ring by its maximal ideal.

The `𝓀[K]`-algebra structure on `𝓀[L]` is Mathlib's canonical
`IsLocalRing.ResidueField.instAlgebra`. It is induced by the integer-ring
algebra `Valuation.HasExtension.instAlgebraInteger`, the restriction of
`algebraMap K L`, which is a local homomorphism by
`Valuation.HasExtension.instIsLocalHomValuationInteger`. The group
structure on `𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]`, and on `Gal(L/K)`, is Mathlib's
`AlgEquiv.aut`. Its identity is the identity automorphism, and its product
is composition, `(ϕ * ψ) x = ϕ (ψ x)`.

The algebra `Algebra K L`, both valuative relations, the valuation
extension and the integral-closure structure are the supplied ones. There
is no replacement valuation, scalar structure or residue quotient. Neither
definition adds an algebraicity, `IsGalois`, finite-dimensionality,
completeness, discrete-valuation, local-field, topology, finite-residue or
prime hypothesis, and there is no preservation or conclusion certificate
premise. No instance is declared.

## Construction

### The residue algebra automorphism (M160.005)

The complete body is

```lean
@[implicit_reducible]
def galoisGroupResidueAlgEquivOfIsIntegralClosure ... (σ : Gal(L/K)) :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] where
  __ := galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
  commutes' := galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap K L σ
```

Write `e` for the published ring equivalence
`galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ`. That definition is
`IsLocalRing.ResidueField.mapEquiv` applied to the published integer-ring
restriction `galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ`; see the
[residue-field definition](Definitions.md). The structure-instance field
`__ := e` fills the forward and inverse functions, the two inverse laws and
the additive and multiplicative laws from `e`. The forward map, the inverse
map and the ring equivalence underlying the result are therefore exactly
those of `e`.

The remaining field `commutes'` is the published theorem
`galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap K L σ` from the
[proof module](Proofs.md), adapted from M160.004. It states, for every
`x : 𝓀[K]`, that `e (algebraMap 𝓀[K] 𝓀[L] x) = algebraMap 𝓀[K] 𝓀[L] x`.
This is exactly the `𝓀[K]`-linearity field of an algebra equivalence. No
other premise or proof is needed.

The source attribute `@[implicit_reducible]` is retained. In Lean 4.34.0 it
only sets reducibility. It lets the definition unfold when Lean compares
implicit and instance-implicit arguments, but keeps it opaque to type-class
search. It declares no instance and no simp lemma.

### The group homomorphism (M160.006)

The data field is `toFun := galoisGroupResidueAlgEquivOfIsIntegralClosure K L`.
So the homomorphism sends `σ` to the algebra automorphism of M160.005, and
its underlying residue map is again the published residue equivalence. The
two proof fields are as follows.

`map_one'` shows that the image of `1 : Gal(L/K)` is the identity:

1. `AlgEquiv.ext` reduces it to pointwise equality on `x : 𝓀[L]`.
2. `IsLocalRing.residue_surjective` gives `a : 𝒪[L]` with
   `x = IsLocalRing.residue 𝒪[L] a`, and `x` is replaced by this class.
3. A `change` restates the goal with the forward map of the published
   residue equivalence:
   `galoisGroupResidueFieldEquivOfIsIntegralClosure K L 1 (residue a) = residue a`.
   The two sides agree with the original goal definitionally: the
   algebra automorphism has the same forward map, and the identity
   automorphism acts as the identity.
4. Rewriting with the published residue evaluation
   `galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L 1 a`
   (adapted from M160.002) turns the left side into the residue class of
   the integer-ring restriction of `1` applied to `a`.
5. `congrArg (IsLocalRing.residue 𝒪[L])` and `Subtype.ext` reduce the goal
   to an equality in `L`.
6. Rewriting with the published forward evaluation
   `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L 1 a`
   (adapted from M139.003) replaces the restricted value by
   `(1 : Gal(L/K)) (a : L)`.
7. `AlgEquiv.one_apply` closes the goal.

`map_mul'` shows, for `σ τ : Gal(L/K)`, that the image of `σ * τ` is the
product of the images:

1. As above, `AlgEquiv.ext` and `IsLocalRing.residue_surjective` reduce the
   goal to the residue class of some `a : 𝒪[L]`.
2. A `change` restates it with the published residue equivalences: the
   map for `σ * τ` applied to `residue a` equals the map for `σ` applied to
   the map for `τ` applied to `residue a`.
3. The published residue evaluation is rewritten three times, for `τ`,
   then `σ`, then `σ * τ`. Both sides become residue classes of values of
   integer-ring restrictions.
4. `congrArg (IsLocalRing.residue 𝒪[L])` and `Subtype.ext` reduce the goal
   to an equality in `L`.
5. The published forward evaluation is rewritten three times, for
   `σ * τ`, then `σ`, then `τ`. The goal becomes
   `(σ * τ) (a : L) = σ (τ (a : L))`.
6. `AlgEquiv.mul_apply σ τ (a : L)` closes the goal.

These two fields are local to the definition. No standalone theorem, simp
lemma or helper declaration is exported.

### Why the group laws are not proved by `rfl`

The source proves both group laws by choosing a quotient representative and
`rfl`. That worked because the original integer-ring restriction was built
from explicit subtype constructors, so its value in `L` reduced to `σ` by
definition. The published integer-ring restriction instead packages
Mathlib's `galRestrict'` with `AlgEquiv.ofAlgHom`; see the
[integer-ring companion](../GaloisIntegerRing/Definitions.md). Mathlib
defines `galRestrict'` through `IsIntegralClosure.equiv`, so the value of
the restricted map in `L` is only propositionally equal to the value of
`σ`. It is given by Mathlib's `algebraMap_galRestrict'_apply` and by the
published forward evaluation. A private author check with
`fail_if_success rfl` confirmed that the representative `rfl` fails for
both laws against the published restriction. The proof therefore uses the
two published evaluation theorems above, as the task specification
suggests.

### Relation to Mathlib's generic residue maps

The residue-level maps reuse Mathlib's `IsLocalRing.ResidueField.mapEquiv`
through the published residue equivalence; no generic machinery is
duplicated. In a private author check, the M160.005 automorphism was shown
equal to Mathlib's `IsLocalRing.ResidueField.mapAlgEquiv'` applied to the
`𝒪[K]`-algebra equivalence
`AlgEquiv.ofAlgHom (galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.toAlgHom) (galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.symm.toAlgHom) _ _`,
by `ext` and `rfl`. The adapted body keeps the source form instead. It
builds directly on the published ring equivalence, so its underlying ring
equivalence is that published map by construction.

Mathlib's `IsLocalRing.ResidueField.mapAut` is not used for M160.006. Its
codomain is the ring automorphism group of the residue field, not the group
of `𝓀[K]`-algebra automorphisms. Using it would also require a group
homomorphism from `Gal(L/K)` to the ring automorphisms of `𝒪[L]`, which is
not published. The group laws are therefore proved directly as above.

## Checks

All checks used `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). The module compiled with no
errors or warnings. Inspection of both complete unapplied declarations
reported kind `definition`, the single level parameter `[u]`, the interface
above, and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

A private, unexported probe also compiled without errors or warnings. It
checked by `rfl` that the M160.005 automorphism's underlying ring
equivalence is the published residue equivalence. That ring equivalence is
also `IsLocalRing.ResidueField.mapEquiv` of the published integer-ring
restriction. The forward and inverse functions agree with those of the
published residue equivalence. The homomorphism of M160.006 evaluates at
`σ` to the M160.005 automorphism, which is the content of the unported
source theorem M160.007. The probe also contained the `mapAlgEquiv'`
agreement and the `fail_if_success rfl` checks described above. These are
author diagnostics. They do not replace machine validation or independent
review.

## Imports and scope

The two explicit imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs`,
  the published [forward and inverse evaluations](../GaloisIntegerRing/Proofs.md)
  of the integer-ring restriction. Only the forward theorem
  `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` is used.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.Proofs`,
  the published [residue proofs](Proofs.md). Both theorems are used: the
  residue evaluation in the group laws and the base-residue fixedness as
  `commutes'`. Through its imports it supplies the published
  [statements](Statements.md) and [residue-field definition](Definitions.md),
  the integer-ring definition, and every Mathlib declaration used here.

The existing `Definitions`, `Statements` and `Proofs` pairs of
`ResidueGalois` and `GaloisIntegerRing` are not modified. The original
broad imports and the namespace opening
`_root_.LocalFieldTheory.IsNonarchimedeanLocalField` are omitted.

Only M160.005 and M160.006 are adapted. This module does not port the
residue-unit wrapper M160.003, the evaluation theorem M160.007, the later
conjugate sums and products, action instances, kernels, stabilizers,
inertia subgroups, or any host reciprocity comparison.

## Source correspondence and changes

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean#L86-L113)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The full file has
SHA-256 `b3c47318364659eb1a14b872f8462a2284f47125b1d84391c5c93a3ba87f2c67`,
which matches the NYLL verification manifest in the attribution supplement.
Lines 1–133 were read.

| Partition unit | Original declaration in `LocalFieldTheory` | Original lines | Adapted definition in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M160.005 | `galoisGroupResidueAlgEquivOfIsIntegralClosure` | 86–94 | `galoisGroupResidueAlgEquivOfIsIntegralClosure` |
| M160.006 | `galoisGroupResidueAlgEquivHomOfIsIntegralClosure` | 96–113 | `galoisGroupResidueAlgEquivHomOfIsIntegralClosure` |

The line ranges include the doc comments and, for M160.005, the attribute
on line 87; the `def` keywords are on lines 88 and 97. The unit identifiers
come from the
[public declaration partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m160).
The original definitions have the same interface and result types. In the
original M160.006 the group is written `Gal(L / K)`, which is the same
notation.

Worker 761 made these changes on 29 October 2026:

- added the `Langlands.NYLL` namespace prefix. The referenced residue
  equivalence and fixedness theorem are now the published prefixed
  declarations of the same names;
- kept the M160.005 body and its `@[implicit_reducible]` attribute as in the
  source;
- kept the M160.006 `toFun` field. The `rfl` proofs of `map_one'` and
  `map_mul'` on residue representatives were replaced by the proofs above,
  for the reason given above. `IsLocalRing.residue_surjective` replaces
  `Ideal.Quotient.mk_surjective`. The two published evaluation theorems and
  Mathlib's `AlgEquiv.one_apply` and `AlgEquiv.mul_apply` replace the
  definitional unfolding;
- rewrote both doc comments to describe the adapted definitions;
- replaced the source's imports with the two published modules above.

The source theorem M160.007 that follows on lines 115–124 is not ported.
The task specification by Worker 106 suggested proving the group laws from
the published integer-ring and residue-representative evaluations. No draft
from another worker was used. The published definitions, theorems and
Mathlib are reused by import and declaration name; their code is not copied
here.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
On 29 October 2026 I found no errata for either registration in the project
notes or the current Library notes. The public partition records no
patch10 change to `ResidueGalois.lean`, and no patch10 code is reused.

The Lean file keeps the original copyright and author header verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex). The existing Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Neither the NOTICE nor the attribution supplement has an entry specific to
`ResidueGalois.lean`. No third-party source is copied into this unit.
