# An embedded finite abelian extension as an abstract subextension

This focused source adaptation implements M402.001 of Naganori Yamaguchi's
NYLL project, `n-yamaguchi-0729/ClassFieldTheory`, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The source file is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`,
definition lines 35–59 and docstring lines 33–34. Its SHA-256 is
`173d65750c2a18cc233fcc94d9fde94e88c7a42709cfb9c27e50bae8e971ba06`.
It is retained under the registered collection
`external-lean-reuse-snapshots-2026-10-21`, with supplement
`nyll-classfieldtheory-fbd320cd-supplement`, at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The source-to-adapted declaration map is:

| Source declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.finiteAbelianAbstractExtensionOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianAbstractExtensionOfEmbedding` |

The entry module is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U001.Definitions`.

## Meaning and exact scope

The definition has the complete source telescope:

```lean
finiteAbelianAbstractExtensionOfEmbedding
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K)
```

Here `ClassFormation` and `intrinsicAbstractBase` refer to the published
`Langlands.NYLL` namespaces. Both carriers are in `Type 0`, as in the source,
and the result is data in `Type 0`. The base and extension carriers are
explicit arguments, followed by the listed instance arguments in their source
order and the explicit embedding. `IsAbelianGalois K L` provides Galoisness
and commutativity of the actual automorphism group `Gal(L / K)`.

The result packages the embedded copy of `L` in the chosen separable closure
of `K`. Its `toFiniteGaloisExtension` field is exactly the existing
`finiteGaloisAbstractExtensionOfEmbedding K L i`. In particular, its closed
subgroup is the subgroup fixing the actual field range of `i`, below the
subgroup fixing the bottom intermediate field
`intrinsicAbstractBase K`.

The `commutative` field concerns the quotient of that base fixing subgroup
by the relative extension subgroup of the embedded field. It uses the actual
multiplicative equivalence
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i` from this
quotient to `Gal(L / K)`. For two quotient elements, the implementation applies
the equivalence's injectivity, rewrites the images of products with `map_mul`,
and uses the commutativity supplied by `IsAbelianGalois K L`.
Thus the construction keeps the supplied embedding and the source quotient
presentation.

The inputs are arbitrary fields with the stated algebraic hypotheses.
No local-field, valuation or topological-field hypothesis is added.
This definition supplies the embedded object; it makes no norm-subgroup or
order-reversal assertion from the later source units.

## Reused declarations

The following published objects supply the construction:

- `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`
  is the existing finite-Galois package together with quotient commutativity.
- `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding`
  from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions`
  supplies the underlying finite-Galois object. Its published internal base
  abbreviation reduces to `intrinsicAbstractBase K`.
- `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`
  from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions`
  identifies the actual quotient group with `Gal(L / K)`. Its field-range
  transport and quotient presentation are retained.
- `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase`,
  `finiteGaloisFieldRangeOfEmbedding` and
  `finiteGaloisClosedFixingSubgroupOfEmbedding`, together with
  `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, supply the exact source
  base, embedded field, fixing subgroup and relative quotient.
- `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal`
  from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Normality.U006.Proofs`
  supplies the published normality instance used to form the quotient group.
- `Mathlib.FieldTheory.Galois.Abelian` supplies `IsAbelianGalois` and its
  Galois and commutativity instances; `map_mul` supplies the compatibility of
  a multiplicative equivalence with products.

The Library was searched by these Lean names before adaptation. This unit
adds only the finite-abelian package constructor; it reuses the underlying
finite-Galois package, field range, subgroup and quotient machinery.

## Modifications and attribution

Worker 543 made these changes to extract M402.001:

1. Prefix the source namespace `LocalClassFieldTheory` with `Langlands.NYLL`.
2. Replace the six source module imports by focused published dependency
   imports and `Mathlib.FieldTheory.Galois.Abelian`.
3. Keep the source `noncomputable section` and the needed opens
   `RamificationTheory`, `CyclicCohomology` and `ClassFormation`; omit the
   unused `LocalFieldTheory` and `KummerTheory` opens.
4. Retain only this source definition and its original docstring, omitting
   all subsequent source units. Add the extraction and modification module
   documentation and this paired Markdown.

The definition name after namespace qualification, binder kinds, carrier
universes, hypotheses, return type and complete body are unchanged. This
unit adds no instances.

The original copyright, Apache-2.0 release and author header is preserved
verbatim. The Library's existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.
