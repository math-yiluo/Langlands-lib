# NYLL M165.009: the abstract norm from a finite separable intermediate field is the field norm (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement`
([target](Statements.md), NYLL source unit M165.009) by the theorem

```lean
theorem relativeNorm_intermediateFieldUnit_val_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (x : Eˣ) :
    relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement K Ω E x
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
Its binders are those of the target, in the same order and with the same
binder kinds, and its type is the target applied to them. Neither has a
level parameter.

The theorem says the following. Let `Ω / K` be a Galois extension with `Ω`
separably closed, and let `E` be an intermediate field that is
finite-dimensional and separable over `K`; `E / K` need not be normal. Write
`G = Gal(Ω / K)`, presented as the subgroup
`(closedFixingSubgroup K Ω ⊥).toSubgroup`, and `H = Gal(Ω / E)`. For
`x ∈ Eˣ`, the published abstract class-formation norm `relativeNorm` from `H`
to `G` of `x` (viewed as an `H`-fixed unit of `Ω`), viewed as an element of
`Ω`, equals `algebraMap K Ω (Algebra.norm K x)`, the image in `Ω` of
Mathlib's field norm `N_{E/K}(x)`. The abstract norm is, written
multiplicatively, the product of `σ(x)` over one representative `σ` of each
left coset `σH`.

## Proof

The module opens a section in which the published local instance
`Langlands.NYLL.PortInternal.M164.d001` is made a local instance with
`attribute [local instance]`. It provides
`Fintype (F →ₐ[k] T)` for a finite separable `F / k`, as
`PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k F)`. The
source uses its own section-local instance `finiteSeparableAlgHomFintype`
(M165.007, source lines 168–173) at this point. That instance is private to
its source section and is not published; its body is the same term as the
body of `M164.d001`. Here it is used to form the product over
`E →ₐ[K] Ω` below. The published statement of M164.003 is written with the
same local instance, so both products carry the same `Fintype` instance.
No copy of M165.007 is published.

The tactic proof is the source proof (lines 209–262) with two changes, both
marked below.

1. `unfold relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement`
   replaces the goal, the target applied to the binders, by its body: the
   equation of the source theorem. (Added; the source theorem states this
   equation directly.)
2. Let `Q` be the coset type `G ⧸ H` (written with the published
   `extensionSubgroup`). `let := Fintype.ofFinite Q` makes it a `Fintype`,
   using the `Finite` instance that the target's `relativeNorm` already
   uses: the published M165.006 instance
   `baseFixingExtensionQuotient_finite_of_isSeparable`, found by instance
   search.
3. `change` rewrites `(relativeNorm … a).1` as
   `relativeNormValue … a`; the published `relativeNorm` (M024.009) has this
   value by definition.
4. `unfold relativeNormValue` replaces the published `relativeNormValue`
   (M024.005) by its body, the sum `∑ q, relativeCosetAction … a q` over the
   cosets `q`, with the coset type made a `Fintype` by `Fintype.ofFinite`.
   (Changed: the source writes `rw [relativeNormValue]`, which fails on the
   published definition; `unfold` performs the intended unfolding.)
5. Two `change` steps restate the goal with the sum written over `Q`, and
   then, since `Additive.toMul` turns a sum in `Additive Ωˣ` into a product
   in `Ωˣ`, as `Units.coeHom Ω` applied to the product of the coset actions.
   `rw [map_prod]` moves the monoid homomorphism `Units.coeHom Ω` inside the
   product, and a further `change` states the goal as a product in `Ω` of the
   coset actions, each viewed in `Ω`.
6. A two-step `calc` finishes. First, Mathlib's `Fintype.prod_equiv`
   reindexes the product along the published bijection
   `baseFixingCosetEquivAlgHom K Ω E` (M165.005) from the cosets `Q` to the
   `K`-embeddings `E →ₐ[K] Ω`. Its pointwise hypothesis is the published
   M165.008 theorem
   `relativeCosetAction_intermediateFieldUnit_val_of_isSeparable K Ω E x`:
   the coset action of `q` on `x`, viewed in `Ω`, is the embedding attached to
   `q` evaluated at `x`. This gives the product of `σ x` over all
   `σ : E →ₐ[K] Ω`. Second, this product is
   `algebraMap K Ω (Algebra.norm K x)` by the published M164.003 theorem
   `algebraMap_norm_eq_prod_embeddings_of_isSepClosed K Ω E (x : E)`,
   used with `.symm`.

In step 6 both published theorems are applied as terms whose types are their
Statement definitions; Lean unfolds those definitions when it checks the
terms against the expected equations.

## Dependencies

The imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U009.Statements`,
  the published target. Through it come `relativeNorm`,
  `galoisAmbientUnitsRep`, `intermediateFieldUnitsEquivGaloisFixed`,
  `closedFixingSubgroup`, `extensionSubgroup`, `fixingSubgroupLeBase` and the
  M165.006 `Finite` instance (module `...SeparableFixedFieldNorm.U006.Proofs`).
- `...SeparableFixedFieldNorm.U008.Proofs`, the published proof of M165.008,
  `relativeCosetAction_intermediateFieldUnit_val_of_isSeparable`. Through it
  comes `relativeCosetAction`.
- `...SeparableFixedFieldNorm.U005.Definitions`, defining
  `baseFixingCosetEquivAlgHom` (M165.005).
- `...SeparableNormProduct.U003.Proofs`, the published proof of M164.003,
  `algebraMap_norm_eq_prod_embeddings_of_isSepClosed`. Through it comes the
  module `...SeparableNormProduct.Statements` that declares the instance
  `Langlands.NYLL.PortInternal.M164.d001`.

`...` abbreviates
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.`
The published `relativeNormValue` comes through these imports from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions`.
From Mathlib the proof uses `Fintype.ofFinite`, `Units.coeHom`, `map_prod`
and `Fintype.prod_equiv`. No helper declaration is introduced, and no
published declaration is modified. The module opens `RamificationTheory`,
`CyclicCohomology` and `ClassFormation`, as the target module does, and, as
in the source, uses a `noncomputable section` and `open scoped BigOperators`.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) over Library commit
`7cb8c3d3219f3b36b03e8b9c949961ebd64f3764` compiled the module with zero
errors and zero warnings. Inspection of the theorem reported kind
`theorem`, no level parameters, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not
acceptance.

## Source correspondence and modification record

The original declaration is the theorem
`LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable`
in Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean#L199-L262)
(SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`):
docstring lines 199–200, statement lines 201–208, proof lines 209–262. It
sits in `section NormAsProduct` (line 166), after the local instance
`finiteSeparableAlgHomFintype` (M165.007, lines 168–173), and uses the
file-level section variables at lines 36–37 and the section variables at
lines 175–176.

| Original declaration | Adapted declaration |
| --- | --- |
| `theorem LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable` (M165.009) | `theorem Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable` (this module) |
| local instance `LocalClassFieldTheory.finiteSeparableAlgHomFintype` (M165.007, private to its section) | not published; the published instance `Langlands.NYLL.PortInternal.M164.d001` (same body) is used through `attribute [local instance]` |
| `LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val_of_isSeparable` (M165.008, used) | same name under `Langlands.NYLL` (published proof) |
| `LocalClassFieldTheory.baseFixingCosetEquivAlgHom` (M165.005, used) | same name under `Langlands.NYLL` (published) |
| `LocalClassFieldTheory.algebraMap_norm_eq_prod_embeddings_of_isSepClosed` (M164.003, used) | same name under `Langlands.NYLL` (published proof) |
| `ClassFormation.relativeNormValue`, `ClassFormation.relativeCosetAction` (M024.005, M024.001, used) | `Langlands.NYLL.ClassFormation.relativeNormValue`, `Langlands.NYLL.ClassFormation.relativeCosetAction` (published) |

Worker 731 made these changes on 15 November 2026:

- the section variables are written as explicit binders, in the source
  order, followed by the theorem's own binder `x`, as in the target. The
  conclusion is written as the target applied to these binders, and the
  proof begins with `unfold` of the target;
- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- the source's local instance M165.007 is replaced by
  `attribute [local instance] Langlands.NYLL.PortInternal.M164.d001` inside
  a section named `NormAsProduct`, as described above;
- the source step `rw [relativeNormValue]` (line 222) becomes
  `unfold relativeNormValue`;
- the source imports are replaced by the four published modules listed
  above. Of the source's opens, `RamificationTheory`, `CyclicCohomology`,
  `ClassFormation` and scoped `BigOperators` are kept; `KummerTheory` and
  `LocalFieldTheory` supply nothing this proof uses and are omitted;
- the docstring and the remaining tactic steps are the source's, unchanged.

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
unchanged in the Library. Worker 731 adapted this proof from the pinned
original, following the route of Worker 85's private development probe
recorded in the task. This support proof discharges no host class-formation,
cohomology or reciprocity target.
