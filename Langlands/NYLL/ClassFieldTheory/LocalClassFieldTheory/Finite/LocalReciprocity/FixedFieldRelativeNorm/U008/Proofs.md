# Relative norms on actual fixed fields: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement`
(NYLL source unit M276.008) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_eq_normUnits`.
Its imports are:

- the statement module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U008.Statements`;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U006.Definitions`,
  for the equivalence `abstractFixedFieldCosetEquivAlgHom` (M276.006);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U007.Proofs`,
  for the theorem `relativeCosetAction_abstractFixedFieldUnit_val` (M276.007);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.U003.Proofs`,
  for the theorem `algebraMap_norm_eq_prod_embeddings_of_isSepClosed`
  (M164.003) and the `Fintype` instance
  `Langlands.NYLL.PortInternal.M164.d001` (M164.001);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.RelativeGalois.U019.Proofs`,
  for the theorem `abstractRelativeFixedField_finiteDimensional` (M099.019).

The statement pair and everything it imports are unchanged.

## Exact target

The theorem's type is exactly
`relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement`. Unfolded, it
says:

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  [Finite
    (K.toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK)]
  [Finite
    ((Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)).toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup
        (Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)) K
        (Langlands.NYLL.ClassFormation.le_baseField K))]
  (x : (abstractRelativeFixedField k Ω hLK)ˣ),
  Langlands.NYLL.ClassFormation.relativeNorm
      (galoisAmbientUnitsRep k Ω) K L hLK
      (abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK (Additive.ofMul x)) =
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K
      (Additive.ofMul
        (Langlands.NYLL.LocalFieldTheory.normUnits
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) x))
```

In words: let `Ω / k` be Galois with `Ω` separably closed, and let `L ≤ K`
be closed subgroups of `Gal(Ω/k)`, with `L` of finite index in `K` and `K`
of finite index in the whole group. Write `Ω^K` and `Ω^L` for the fixed
fields of `K` and `L`. For a unit `x` of `Ω^L`, the class-formation
relative norm of `x`, viewed as an `L`-fixed vector of `Ωˣ`, is the
`K`-fixed vector given by the field norm `N_{Ω^L/Ω^K}(x)`.

## Proof

The proof

1. introduces the binders, naming the two finiteness instances `hfinite`
   (finite index of `L` in `K`) and `hKabsolute` (finite index of `K`), as
   in the source;
2. installs the local instance
   `FiniteDimensional (Ω^K) (Ω^L)` from the published theorem
   `abstractRelativeFixedField_finiteDimensional k Ω K L hLK hKabsolute hfinite`,
   and `Algebra.IsSeparable (Ω^K) (Ω^L)` by
   `Algebra.isSeparable_tower_bot_of_isSeparable` from the separability of
   `Ω` over `Ω^K`;
3. reduces the equality in the fixed-vector subtype to an equality in `Ω`
   by `Subtype.ext`, `Additive.ext` and `Units.ext`;
4. unfolds `relativeNorm` and `relativeNormValue` by `change` and `rw`, so
   that the left side is the coercion to `Ω` of the product, over the
   finite quotient `Q = K ⧸ (L as a subgroup of K)` (with the `Fintype`
   instance `Fintype.ofFinite Q`), of the coset actions
   `relativeCosetAction`; `map_prod` for `Units.coeHom Ω` moves the
   coercion inside the product;
5. finishes with a two-step `calc`:
   - `Fintype.prod_equiv` along the bijection
     `abstractFixedFieldCosetEquivAlgHom k Ω K L hLK` between the cosets and
     the `Ω^K`-embeddings `Ω^L →ₐ[Ω^K] Ω`, with the termwise identity
     `relativeCosetAction_abstractFixedFieldUnit_val k Ω K L hLK x`, turns
     the product over cosets into `∏ σ : Ω^L →ₐ[Ω^K] Ω, σ x`;
   - the symmetric form of
     `algebraMap_norm_eq_prod_embeddings_of_isSepClosed (Ω^K) Ω (Ω^L) x`
     identifies that product with `algebraMap (Ω^K) Ω (Algebra.norm (Ω^K) x)`,
     which is the right side.

The product over embeddings uses the `Fintype` instance
`Langlands.NYLL.PortInternal.M164.d001`, made a local instance by
`attribute [local instance]`, so that it is the instance of the
M164.003 statement.

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`
(SHA-256
`ab3ee25eed6dbccd721f18245bc5f17aea6fbe8e7631a11f41e9eb88032c1e4c`),
theorem `relativeNorm_abstractFixedFieldUnit_eq_normUnits`: docstring lines
189–191, signature lines 192–208, proof lines 209–273.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`.
- After the `intro`, the tactic proof is the original one, line for line.
  Its cited declarations (`abstractRelativeFixedField_finiteDimensional`,
  `relativeNormValue`, `relativeCosetAction`,
  `abstractFixedFieldCosetEquivAlgHom`,
  `relativeCosetAction_abstractFixedFieldUnit_val`,
  `algebraMap_norm_eq_prod_embeddings_of_isSepClosed`) are the published
  `Langlands.NYLL` declarations of the same source units, applied to the
  same explicit arguments.
- The source file declares the local instance
  `finiteSeparableAlgHomFintypeRelative` (M276.001), the `Fintype`
  structure on `E →ₐ[F] T` given by
  `PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable F E)`.
  This module instead makes the published declaration
  `Langlands.NYLL.PortInternal.M164.d001` (M164.001), which has the same
  binders and the same body, a local instance.
- The imports replace the original imports. The original
  `noncomputable section` and `open scoped BigOperators` are kept; the
  namespace openings are reduced to
  `Langlands.NYLL.CyclicCohomology` and `Langlands.NYLL.ClassFormation`.
  All other declarations of the module are omitted.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56 and a dated reuse and checking record by Worker 537. The retained
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged.

Worker 537 reused Worker 56's shared Task 7285 draft, revision 1
(content key `e13f9a5e1fa418b8c08a13dacffec3d091cf55a393a76c7e5ddd8237ffc51652`),
on 16 November 2026. The mathematical proof is unchanged; the additional
header records this reuse. Worker 56 is credited as a coauthor in the
submission.

No global instance or simp attribute is installed. The development check
on 16 November 2026 reports no errors or warnings.
