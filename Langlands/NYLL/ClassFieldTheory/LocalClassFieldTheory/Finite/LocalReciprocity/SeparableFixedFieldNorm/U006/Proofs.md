# NYLL M165.006: the coset space of the base fixing subgroup is finite (proof and instance)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparableStatement`
([target](Statements.md), NYLL source unit M165.006) by the theorem

```lean
theorem baseFixingExtensionQuotient_finite_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    baseFixingExtensionQuotient_finite_of_isSeparableStatement K Ω E
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
Its binders are those of the target, in the same order and with the same
binder kinds, and its type is the target applied to them. Neither has a
level parameter. The target is a reducible `abbrev`, so the module then
registers the theorem as a global instance, as the source does:

```lean
attribute [instance] baseFixingExtensionQuotient_finite_of_isSeparable
```

The theorem says the following. Let `Ω / K` be a Galois extension with `Ω`
separably closed, and let `E` be an intermediate field that is
finite-dimensional and separable over `K`. Write `G = Gal(Ω / K)`, presented
as the subgroup `(closedFixingSubgroup K Ω ⊥).toSubgroup`, and
`H = Gal(Ω / E)`. Then the type of left cosets of `H` in `G` is finite. After
the instance attribute, any module importing this one finds that `Finite`
instance by instance search. This is what the relative norm `relativeNorm`
needs in the source's next theorem M165.009.

## Proof

The proof is the source proof term, unchanged:

```lean
(baseFixingCosetEquivAlgHom K Ω E).finite_iff.mpr inferInstance
```

1. The published definition
   `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetEquivAlgHom K Ω E`
   (M165.005, [definition](../U005/Definitions.md)) is an equivalence between
   the coset type of the target and `E →ₐ[K] Ω`, the `K`-embeddings of `E`
   into `Ω`. It is `Equiv.ofBijective` of the published restriction map
   `baseFixingCosetToAlgHom`, with bijectivity given by the published proofs
   `Langlands.NYLL.PortInternal.M165.d004` (injectivity) and
   `Langlands.NYLL.PortInternal.M165.d003` (surjectivity). It is where the
   hypotheses `[IsSepClosed Ω]`, `[FiniteDimensional K E]` and
   `[Algebra.IsSeparable K E]` are used.
2. Mathlib's `Equiv.finite_iff` states that for an equivalence `e : α ≃ β`,
   `Finite α ↔ Finite β`. Its `.mpr` direction reduces the goal to
   `Finite (E →ₐ[K] Ω)`. Since the target is an `abbrev`, its body is the
   `Finite` statement on the coset type, and the term has the target's type
   up to unfolding the abbreviation.
3. `inferInstance` closes `Finite (E →ₐ[K] Ω)`. A private probe with
   `#synth` showed that instance search finds Mathlib's anonymous instance
   `instFiniteAlgHomOfFinite` (in
   `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`): if `S` is a
   finite module over a commutative semiring `R` and `K` is a field, then
   `S →ₐ[R] K` is finite. It applies with `R = K`, `S = E` and field `Ω`,
   using `[FiniteDimensional K E]`.

## Dependencies

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U006.Statements`
  is the published target. Through it come `closedFixingSubgroup`,
  `extensionSubgroup` and `fixingSubgroupLeBase`.
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U005.Definitions`
  supplies `baseFixingCosetEquivAlgHom`. Through it come the published
  proofs `PortInternal.M165.d003` and `d004`.
- From Mathlib: `Equiv.finite_iff` and the instance
  `instFiniteAlgHomOfFinite`.

No other Library result and no helper declaration is used. The published
target and definitions are used by name and none of them is modified. The
module opens `RamificationTheory` and `CyclicCohomology`, as the published
definitions module does. The proof needs neither opening, since the target
and `baseFixingCosetEquivAlgHom` are in the module's own namespace.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with zero errors and zero warnings. Inspection of the theorem reported kind
`theorem`, no level parameters, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. A private client module that imports
this one proved the target's `Finite` statement on the coset type, written
out in full, by `inferInstance`. This confirms the instance registration.
These development checks are not acceptance.

## Source correspondence and modification record

The original declaration is the instance
`LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable` in
Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean#L154-L162)
(SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`).
It sits in `section CosetsAndEmbeddings`. Its docstring is at line 154, the
declaration at lines 155–161 and its body at line 162. It uses the file-level
section variables at lines 36–37 and the section variable `E` at line 41.

| Original declaration | Adapted declaration |
| --- | --- |
| `noncomputable instance LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable` (M165.006) | `theorem Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable` with `attribute [instance]` (this module) |
| `LocalClassFieldTheory.baseFixingCosetEquivAlgHom` (M165.005, used) | `Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetEquivAlgHom` (published) |

Worker 368 made these changes on 15 November 2026:

- the `noncomputable instance` becomes a `theorem` of the published target,
  followed by `attribute [instance]` for it, following the published
  precedent `localSeparableValuationHasExtension` (module
  `...LocalReciprocity.LocalResidueDatum.U008.Proofs`). The `noncomputable`
  modifier is dropped because a theorem needs none;
- the section variables the instance takes are written as explicit binders,
  in the source order, as in the target;
- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the source imports are replaced by the two published modules above. Of
  the source's opens, only `RamificationTheory` and `CyclicCohomology` are
  kept; the `noncomputable section` and the section structure are omitted;
- the docstring and the proof term are the source's, unchanged.

The registered source is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
unchanged in the Library. This support proof discharges no host
class-formation, cohomology or reciprocity target.
