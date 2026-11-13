# The NYLL unramified class for supplied local-field data

This module defines the proposition
`Langlands.LocalClassField.NYLL.SuppliedUnramifiedValuedExtensionStatement`
in `Langlands.ClassFieldTheory.Local.NYLL.SuppliedUnramifiedStatement`. It is a
statement target for a separate proof; this module proves nothing.

The target is a bridge between two formulations of "the extension is
unramified" for arbitrary supplied realizations of p-adic fields. One is the
ported NYLL class
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`,
on which the NYLL unramified normalization theorems depend. The other is the
host premise "relative ramification index one" for the explicit supplied
integer scalars. The host proposition
`Langlands.LocalClassField.NYLL.RamifiedGeometricNormalizationTransferStatement`
uses the host premise. The NYLL finite reciprocity unit 4d (Task 926) needs the
bridge to apply the NYLL theorems to supplied data.

## Full telescope and conclusion

```lean
def SuppliedUnramifiedValuedExtensionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    letI := TF.topology
    letI := TF.valuativeRel
    letI := TF.localField
    letI := TE.topology
    letI := TE.valuativeRel
    letI := TE.localField
    ∀ [Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
        (ValuativeRel.valuation E.Carrier)],
      Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier] ∧
        ∀ [Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier]],
          Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
              F.Carrier E.Carrier ↔
            (letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TE
             (IsLocalRing.maximalIdeal TE.Integers).ramificationIdx TF.Integers = 1)
```

The universes `u` and `v` of the two fields are independent. Every prime `p`
is allowed.

### Data

- `F` and `E` are arbitrary p-adic fields of the Library (`PadicField`), with
  an arbitrary supplied `Algebra F.Carrier E.Carrier` compatible with the
  structure maps from `Padic p` and finite-dimensional over `F.Carrier`.
- `TF` and `TE` are arbitrary supplied `PadicField.TopologicalData`. All
  structures used are those of the supplied data: `TF.topology`,
  `TF.valuativeRel` and `TF.localField : IsNonarchimedeanLocalField F.Carrier`,
  and likewise for `TE`. No canonical or chosen structure is substituted.
- `𝒪[F.Carrier]` is Mathlib's scoped notation for
  `Valuation.integer (ValuativeRel.valuation F.Carrier)`, the valuation ring of
  `TF.valuativeRel`. It is by definition the Library's `TF.Integers`; likewise
  `𝒪[E.Carrier]` is `TE.Integers`.

### Valuation compatibility

The statement quantifies over every instance of Mathlib's
`Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
(ValuativeRel.valuation E.Carrier)`, compatibility of the supplied valuations
along the supplied `algebraMap`. This is a proposition, so the quantifier only
records the premise. The published theorem
`Langlands.LocalClassField.NYLL.suppliedRelativeValuationExtension` proves the
premise for all supplied data. The statement is formulated with the binder
rather than that theorem so that it does not import a proof. Through this
instance, Mathlib's `Valuation.HasExtension.instAlgebraInteger` gives the
algebra `𝒪[F.Carrier] → 𝒪[E.Carrier]` that restricts `algebraMap`. Both
`Module.Finite` occurrences and the NYLL class refer to this Mathlib algebra.

### First conjunct: finiteness

`Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier]` asserts that the extension
valuation ring is a finitely generated module over the base valuation ring,
for Mathlib's integer algebra. This is the module structure that the NYLL
class takes as an instance parameter. The published
`Langlands.LocalClassField.NYLL.RelativeIntegerStructureStatement` asserts
finiteness for the explicit scalars `relativeIntegerAlgebra TF TE` instead. The
first conjunct is the same fact for Mathlib's algebra.

### Second conjunct: the unramified class

For every instance of that finiteness (again a proposition), the NYLL class
for `F.Carrier` and `E.Carrier` with all supplied instances holds if and only
if Mathlib's `Ideal.ramificationIdx` of the maximal ideal of `TE.Integers` over
`TF.Integers` is one. On the right, the algebra
`PadicField.TopologicalData.relativeIntegerAlgebra TF TE` is installed. It is
the published explicit algebra given by `relativeIntegerMap TF TE`, the
restriction of the supplied `algebraMap F.Carrier E.Carrier` to the supplied
valuation rings. The right-hand side is literally the premise used in
`RamifiedGeometricNormalizationTransferStatement` and
`FiniteInertiaFieldUnramifiedStatement`.

The class field states the same ramification-index equation for Mathlib's
integer algebra. The two algebras have the same underlying map, so the
equivalence is expected. It must still be proved, because the two algebra
structures are different terms and their scalar actions are not
definitionally equal for an arbitrary supplied `Algebra F.Carrier E.Carrier`.

No ramification hypothesis, residue-degree hypothesis or conclusion
certificate is added. Neither side asserts that a given extension is
unramified.

## Provenance

This is an internal supplied-data bridge, not a declaration of the original
source. Its two sides come from:

| Ingredient | Origin |
| --- | --- |
| `IsUnramifiedValuedExtension` | Adaptation of NYLL M161.001, `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean` lines 32–44 at commit `fbd320cd8b1b06487c58227e92eb135794267709` (registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) |
| `relativeIntegerAlgebra`, `TopologicalData.Integers` | Published host modules `Langlands.LocalField.RelativeIntegers` and `Langlands.LocalField.Normalization.Definitions` |
| Relative-ramification premise | The published host target `RamifiedGeometricNormalizationTransferStatement` |

The finiteness conjunct is needed because the class takes Mathlib's
`Module.Finite` as an instance parameter, while the published
`RelativeIntegerStructureStatement` uses explicit scalars. The NYLL
unramified normalization theorem
`ClassFieldTheory.finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow`
(M269.023 in the port partition) requires the NYLL class. Applying that
theorem to supplied data therefore needs this bridge. The NYLL integer
algebra is Mathlib's, as recorded in the class module's documentation.

Both sides express ramification index one of the maximal ideal of the
extension valuation ring over the base valuation ring. No theorem of the
original source or of the literature is translated here.

## Imports and scope

The direct imports are `Langlands.LocalField.RelativeIntegers` (supplied
integer rings and the explicit relative algebra, with their Mathlib support)
and the module of the ported class. No proof module is imported.

This module adds only the Prop-valued definition. It proves neither
conjunct. It does not construct an Artin map and claims no normalization,
reciprocity, inertia or residue-action result.

## Development check

The module compiles in the approved Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment
(environment artifact `5c94c648-e8dc-4002-a50a-071ebf3f6096`) with no errors or
warnings.
Inspection of the declaration reports a definition returning `Prop` with
universe parameters `u, v`. Its dependencies use only `propext`,
`Classical.choice` and `Quot.sound`.

## Attribution

Worker 8 formulated and implemented this target and wrote this documentation
in an earlier project instance; the text was carried over unchanged in
substance. Worker 926 rechecked it in the current environment and submits it
under Task 926. The ported class is an adaptation of Naganori Yamaguchi's NYLL
source (Apache-2.0; original header retained in the class module). The reused
host definitions were published earlier.
