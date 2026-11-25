# On `p`-adic fields the general Artin map is the Library's geometric symbol

Module `Langlands.ClassFieldTheory.Local.Artin.PadicComparison`, name space
`Langlands.ClassFieldTheory.Local.Artin`. This file belongs to the Library; it compares the local
Artin map of the NYLL library (`FiniteArtin.lean`) with the Library's own finite Artin symbols on
`p`-adic fields.

Let `F` be a `p`-adic field (the Library's `PadicField p`, a finite extension of `ℚ_p`) with a
supplied topological datum `T : F.TopologicalData` (topology, valuative relation and the certificate
that `F.Carrier` is a nonarchimedean local field), and `D` a finite abelian extension of `F.Carrier`.

- **Comparison** (`geometricSymbol_eq_geometricFiniteArtin`): the Library's geometric finite Artin
  symbol `FiniteArtinSystemExistence.geometricSymbol F D`, built from the Library's cohomological
  local class field theory, is the general geometric Artin map `geometricFiniteArtin F.Carrier D` for
  the local-field structure of `T`.
- In the arithmetic normalization (`artinSymbol_eq_arithmeticFiniteArtin`): the Library's arithmetic
  symbol `FiniteArtinSymbol.artinSymbol F D` is `arithmeticFiniteArtin F.Carrier D`.

Along the way:

- `padicGeometricArtin_unramified`: NYLL's geometric map satisfies the Library's unramified
  normalization in supplied data — on a relatively unramified level `D` with datum `TD`, the inverse
  of the symbol of an element `a` with `T.ord a = 1` induces `x ↦ x ^ q` on residues,
  `TD.discreteValuation ((Art a)⁻¹ x − x ^ q) < 1` for `TD.discreteValuation x ≤ 1`, `q` the residue
  cardinality of `T`.
- `nyllGeometricFamily_relation`: NYLL's maps on the Library's finite abelian extensions
  (`nyllGeometricFamily F T`) satisfy the Library's whole relation
  `GeometricFiniteArtinSystemRelation F T`, the normalization on every (possibly ramified) finite
  abelian level included; hence (`nyllGeometricFamily_eq_geometricFamily`) the family is the
  Library's `FiniteArtinSystemExistence.geometricFamily F T`.

## Main declarations

`{p : ℕ} [Fact p.Prime]`, `F : PadicField.{u} p`, `T : F.TopologicalData`.

```lean
def padicGeometricArtin (D : PadicField.{u} p) [Algebra F.Carrier D.Carrier]
    [IsScalarTower (Padic p) F.Carrier D.Carrier] [IsAbelianGalois F.Carrier D.Carrier]
    (_ : D.TopologicalData) : F.Carrierˣ →* Gal(D.Carrier/F.Carrier)
  -- geometricFiniteArtin F.Carrier D.Carrier, for the structure of T

theorem padicGeometricArtin_unramified (D : PadicField.{u} p) [Algebra F.Carrier D.Carrier]
    [IsScalarTower (Padic p) F.Carrier D.Carrier] [IsAbelianGalois F.Carrier D.Carrier]
    (TD : D.TopologicalData)
    (h : letI := PadicField.TopologicalData.relativeIntegerAlgebra T TD
      (IsLocalRing.maximalIdeal TD.Integers).ramificationIdx T.Integers = 1)
    (a : F.Carrierˣ) (ha : T.ord (a : F.Carrier) = 1) (x : D.Carrier)
    (hx : TD.discreteValuation x ≤ 1) :
    TD.discreteValuation ((padicGeometricArtin F T D TD a).symm x - x ^ T.residueCardinality) < 1

def nyllGeometricFamily : letI := T.topology; LocalClassField.FiniteArtinFamily F.Carrier
theorem nyllGeometricFamily_relation :
    LocalClassField.GeometricFiniteArtinSystemRelation F T (nyllGeometricFamily F T)
theorem nyllGeometricFamily_eq_geometricFamily :
    nyllGeometricFamily F T = LocalClassField.FiniteArtinSystemExistence.geometricFamily F T

theorem geometricSymbol_eq_geometricFiniteArtin (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D] (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    LocalClassField.FiniteArtinSystemExistence.geometricSymbol F D a =
      geometricFiniteArtin F.Carrier D a
theorem artinSymbol_eq_arithmeticFiniteArtin (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D] (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ClassFieldTheory.Local.FiniteArtinSymbol.artinSymbol F D a = arithmeticFiniteArtin F.Carrier D a
```

## Proofs

- Unramified normalization. With the local-field structures of `T` and `TD`, the Library's
  supplied-data comparisons give the valuation extension (`suppliedRelativeValuationExtension`),
  finiteness of the integer rings and NYLL's class `IsUnramifiedValuedExtension` from the
  ramification index (`suppliedUnramifiedValuedExtension`), and NYLL's valuation as minus `T.ord`
  (`suppliedValuationSign`). NYLL's residue normalization
  (`abelianLocalArtinMap_inverseUniformizer_residue_pow`, at `a⁻¹`, of NYLL-valuation one) gives
  `z ∈ 𝒪[D]` with `z = (Art a)⁻¹ x` and the same residue as `x ^ q`; the Library's
  `suppliedResidueCongruence` turns equality of residues into `TD.discreteValuation (z − x^q) < 1`.
  `T.Integers` is `𝒪[F.Carrier]` and `T.residueCardinality` is `Nat.card 𝓀[F.Carrier]` by definition.
- The relation. Onto, kernel and restriction come from `FiniteArtin.lean`; the normalization on a
  ramified level is the Library's `UniverseZero.ramifiedGeometricNormalizationTransfer`, which
  deduces it for any Artin family from the unramified normalization and the compatibility with the
  restriction to the maximal unramified subextension (`finiteInertiaField`).
- The Library's uniqueness theorem `geometricFiniteArtinSystemUniqueness` (two continuous families
  with the relation are equal) and its existence (`FiniteArtinSystemExistence.geometricFamily_relation`)
  identify the families. For general `D`, embed `D` into `AlgebraicClosure F.Carrier`; its image is
  one of the Library's finite abelian extensions, and both symbols are compatible with restriction
  along `D ≅ image` (`restrictNormalHom_geometricSymbol`, `restrictNormalHom_geometricFiniteArtin`).
  The arithmetic form follows from `geometricSymbol_symm`.

## Declarations used

- From the NYLL copy (`…/LocalReciprocity/UniverseFrobenius.lean`):
  `LocalClassFieldTheory.Universe.abelianLocalArtinMap_inverseUniformizer_residue_pow`.
- From the Library (copied into this workspace from the Library's tree, see the report):
  `FiniteArtinSystemExistence.geometricSymbol`, `geometricSymbol_symm`, `geometricFamily`,
  `geometricFamily_relation`, `restrictNormalHom_geometricSymbol`, `fieldAlgebra`, `fieldTower`,
  `fieldAbelian` (`ClassFieldTheory/Local/FiniteArtinSystemExistenceProof.lean`),
  `geometricFiniteArtinSystemUniqueness` (`FiniteArtinSystemUniquenessProof.lean`),
  `GeometricFiniteArtinSystemRelation` (`FiniteArtinSystemStatement.lean`),
  `FiniteArtinSymbol.artinSymbol` (`FiniteArtinSymbol.lean`),
  `UniverseZero.ramifiedGeometricNormalizationTransfer`, `finiteInertiaField`,
  `finiteInertiaPadicField`, `finiteInertiaField_isAbelianGalois`
  (`UniverseZero/RamifiedGeometricNormalizationTransferProof.lean`, `UniverseZero/FiniteInertiaField.lean`),
  `UniverseZero.suppliedRelativeValuationExtension` (`Supplied/SuppliedValuationProof.lean`),
  `UniverseZero.suppliedResidueCongruence` (`Supplied/SuppliedResidueProof.lean`),
  `UniverseZero.suppliedUnramifiedValuedExtension`, `UniverseZero.suppliedValuationSign`
  (`General/SuppliedUnramifiedProof.lean`, `General/SuppliedValuationSignProof.lean`),
  `PadicField.TopologicalData` and its `Integers`, `ord`, `discreteValuation`, `residueCardinality`
  (`LocalField/Definitions.lean`, `LocalField/Normalization/Definitions.lean`).

## Sources

- J.-P. Serre, *Local Fields*, chapter XIII, §4, Propositions 12 and 13, p. 197, and the Corollary
  of Proposition 13 (units go onto inertia), p. 198: the reciprocity map is determined by its
  compatibility with restriction and its values on unramified extensions.
- J. S. Milne, *Class Field Theory* (version 4.03), chapter I, §1, Theorem 1.1 (uniqueness of the
  local Artin map with properties (a) and (b)), p. 20.
