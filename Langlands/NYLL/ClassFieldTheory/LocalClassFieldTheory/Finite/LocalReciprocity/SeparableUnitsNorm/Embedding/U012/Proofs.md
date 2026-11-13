# NYLL M096.012: norm invariance under an embedded field realization

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.normUnits_embeddedExtensionAlgEquivStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.normUnits_embeddedExtensionAlgEquiv`.
The theorem's type is exactly that proposition applied to its source
parameters, `normUnits_embeddedExtensionAlgEquivStatement K Ω L i x`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Embedding.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem is stated in the source's section telescope, with the source's
`omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in`. Its
parameters are therefore, in this order, explicit `K Ω : Type`, the instances
`[Field K] [Field Ω] [Algebra K Ω]`, explicit `L : Type`, the instances
`[Field L] [Algebra K L]`, an explicit `K`-algebra homomorphism
`i : L →ₐ[K] Ω` and an explicit unit `x : Lˣ`. No Galois or
finite-dimensional hypothesis is used, exactly as in the published
proposition.

Unfolding the published proposition gives

```lean
normUnits K (AlgHom.fieldRange i)
    (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv x) =
  normUnits K L x
```

Here `normUnits K L` is the published unit-level algebra norm
`Units.map (Algebra.norm K) : Lˣ →* Kˣ` of
`Langlands.NYLL.LocalFieldTheory`, and `AlgEquiv.ofInjectiveField i` is
Mathlib's `K`-algebra isomorphism from `L` onto the image of the field
homomorphism `i`. The statement says that the norm of `x` from `L` to `K`
equals the norm of its image in the realization `i(L) ⊆ Ω`.

## Implemented proof

The complete proof body is

```lean
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofInjectiveField i) (x : L)
```

`Units.ext` reduces the equality of units in `Kˣ` to equality of their
underlying elements of `K`. Since `normUnits` is `Units.map (Algebra.norm K)`,
these are `Algebra.norm K (AlgEquiv.ofInjectiveField i x)` and
`Algebra.norm K x`, up to definitional unfolding. Mathlib's
`Algebra.norm_eq_of_algEquiv`, which states
`Algebra.norm R (e x) = Algebra.norm R x` for an algebra isomorphism `e`,
closes the goal with `e = AlgEquiv.ofInjectiveField i`.

The `apply Units.ext` step works directly on the theorem's stated type, so,
apart from stating the type as the published proposition, this is the
original proof verbatim. The source's two local instances
`embeddedFieldRangeFiniteDimensional` and `embeddedFieldRangeIsGalois`
(M096.010–011) are not needed: the published proposition and this proof
omit the finite-dimensional and Galois hypotheses they would serve. No
auxiliary declaration, extra hypothesis, instance or `simp` registration is
introduced. The development check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.normUnits_embeddedExtensionAlgEquivStatement`
  in SeparableUnitsNorm.Embedding.Statements.
- The published definition `Langlands.NYLL.LocalFieldTheory.normUnits`
  (ValuedFieldTheory.LocalField.NormUnits.U002.Definitions), reached through
  the unchanged Statements import chain.
- Mathlib's `Units.ext`, `Algebra.norm_eq_of_algEquiv`
  (`Mathlib/RingTheory/Norm/Basic.lean`), `AlgEquiv.ofInjectiveField`
  (`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`) and `AlgHom.fieldRange`,
  all available through the Statements module's imports.

No other proof and no host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:356–364`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean#L356-L364).
Line 356 is the retained `omit ... in`, 357 the retained docstring, 358–361
the signature and 362–364 the proof. The section variables are
`(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]` at
lines 36–37 and, in section `EmbeddedFiniteGaloisExtension`,
`(L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
(i : L →ₐ[K] Ω)` at lines 344–346. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m096)
places this proof at M096.012 (source unit lines 358–368) after M096.011.END.
The whole-file SHA-256 is
`b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `normUnits_embeddedExtensionAlgEquiv` (M096.012) | Published `normUnits_embeddedExtensionAlgEquivStatement` in SeparableUnitsNorm.Embedding.Statements |
| Proof `normUnits_embeddedExtensionAlgEquiv` | This theorem of the same adapted name in SeparableUnitsNorm.Embedding.U012.Proofs |
| `LocalFieldTheory.normUnits` | Existing published `Langlands.NYLL.LocalFieldTheory.normUnits` |
| Local instances `embeddedFieldRangeFiniteDimensional`, `embeddedFieldRangeIsGalois` (M096.010–011) | Not used |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, opens only
`LocalFieldTheory` (the source also opens `RamificationTheory`,
`KummerTheory`, `ClassFormation`, `CyclicCohomology`, `BigOperators` and a
`noncomputable section`, unused here), keeps the source section variables and
`omit` clause, and states the theorem's type as the published proposition
applied to `K Ω L i x`.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 96's dated modification
record. Worker 96 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M096.012. The norm-subgroup equality M096.013, the
abstract relative norm comparisons of M096 and any host class-formation, cup,
transfer, Tate or reciprocity target are separate work.
