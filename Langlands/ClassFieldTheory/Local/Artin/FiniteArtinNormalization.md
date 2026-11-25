# The arithmetic normalization of the local Artin map on unramified extensions

Module `Langlands.ClassFieldTheory.Local.Artin.FiniteArtinNormalization`, name space
`Langlands.ClassFieldTheory.Local.Artin`. This file belongs to the Library; it states the
unramified normalization of the local Artin map of the NYLL library (`FiniteArtin.lean`) in NYLL's
vocabulary and in the Library's.

On a finite unramified extension, the arithmetic Artin map `arithmeticFiniteArtin K L` sends
`x ∈ Kˣ` to the arithmetic Frobenius (the automorphism inducing `y ↦ y ^ q` on residues, `q` the
order of the residue field of `K`) raised to the normalized order `ord(x)`:

- **NYLL's vocabulary** (`arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow`): `L` a nonarchimedean
  local field with `Valuation.HasExtension` of the valuations and NYLL's class
  `IsUnramifiedValuedExtension K L`; the Frobenius is NYLL's
  `arithmeticFrobeniusOfUnramifiedValuation K L`.
- **The Library's vocabulary** (`arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow`): `E` a
  finite Galois intermediate field of Mathlib's `SeparableClosure K` with `ArithmeticUnramified K E`
  (the Library's unramified stages, on which its local invariant is computed); the Frobenius is the
  Library's `finiteUnramifiedFrobenius K E hE`, the order the Library's `normalizedUnitOrder K`. Such
  a stage is cyclic, hence abelian (`isAbelianGalois_of_arithmeticUnramified`).

NYLL's normalized valuation is minus the Library's order
(`valuationMap_eq_neg_normalizedUnitOrder`); this is why NYLL's own map is geometric.

## Main declarations

`K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`.

```lean
theorem valuationMap_eq_neg_normalizedUnitOrder (x : Kˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) =
      -normalizedUnitOrder K (.ofMul x)
theorem valuationMap_inv_eq_normalizedUnitOrder (x : Kˣ) :
    valuationMap K (Additive.ofMul x⁻¹) = normalizedUnitOrder K (.ofMul x)

-- L : Type v, [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
-- [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
-- [Valuation.HasExtension (valuation K) (valuation L)] [IsUnramifiedValuedExtension K L]
theorem arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow (x : Kˣ) :
    arithmeticFiniteArtin K L x =
      arithmeticFrobeniusOfUnramifiedValuation K L ^ normalizedUnitOrder K (.ofMul x)
theorem arithmeticFiniteArtin_of_normalizedUnitOrder_eq_one (π : Kˣ)
    (hπ : normalizedUnitOrder K (.ofMul π) = 1) :
    arithmeticFiniteArtin K L π = arithmeticFrobeniusOfUnramifiedValuation K L
theorem arithmeticFiniteArtin_residue_pow (π : Kˣ) (hπ : normalizedUnitOrder K (.ofMul π) = 1)
    (x : 𝒪[L]) :
    ∃ z : 𝒪[L], (z : L) = arithmeticFiniteArtin K L π (x : L) ∧
      residue 𝒪[L] z = residue 𝒪[L] x ^ Nat.card 𝓀[K]

theorem spectral_hasExtension (X : Type u) [Field X] [Algebra K X] [FiniteDimensional K X] :
    letI := FiniteExtension.valuativeRel K X
    (valuation K).HasExtension (valuation X)
def baseIntegerEquiv : 𝒪[K] ≃+* LocalGalois.baseIntegers K

-- E : IntermediateField K (SeparableClosure K), [FiniteDimensional K E] [IsGalois K E]
theorem isUnramifiedValuedExtension_of_arithmeticUnramified (hE : ArithmeticUnramified K E) :
    letI := FiniteExtension.normedField K E
    letI := FiniteExtension.valuativeRel K E
    haveI := FiniteExtension.isLocalField K E
    haveI := spectral_hasExtension K E
    IsUnramifiedValuedExtension K E
theorem isAbelianGalois_of_arithmeticUnramified (hE : ArithmeticUnramified K E) :
    IsAbelianGalois K E
theorem residueHom_arithmeticFiniteArtin (hE : ArithmeticUnramified K E) (π : Kˣ)
    (hπ : normalizedUnitOrder K (.ofMul π) = 1) (y : ResidueField (extensionIntegers K E)) :
    haveI := isAbelianGalois_of_arithmeticUnramified K E hE
    residueHom K E (arithmeticFiniteArtin K E π) y = y ^ Nat.card (ResidueField (baseIntegers K))
theorem arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius (hE : ArithmeticUnramified K E) (π : Kˣ)
    (hπ : normalizedUnitOrder K (.ofMul π) = 1) :
    haveI := isAbelianGalois_of_arithmeticUnramified K E hE
    arithmeticFiniteArtin K E π = finiteUnramifiedFrobenius K E hE
theorem arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow (hE : ArithmeticUnramified K E)
    (x : Kˣ) :
    haveI := isAbelianGalois_of_arithmeticUnramified K E hE
    arithmeticFiniteArtin K E x =
      finiteUnramifiedFrobenius K E hE ^ normalizedUnitOrder K (.ofMul x)
```

The file also declares three local instances, `spectralBaseNormedField`, `spectralBaseUltrametric`,
`spectralBaseComplete` (the Library's `LocalGalois.localNormedField K` and its properties), used by
the Library's residue action `residueHom`.

## Proofs

- The order: both are the image of the valuation under Mathlib's
  `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`, read additively, with opposite signs.
- NYLL's form is NYLL's `abelianLocalArtinMonoidHom_eq_frobenius_zpow` at `x⁻¹`; the residue action
  is NYLL's `abelianLocalArtinMap_inverseUniformizer_residue_pow` at `π⁻¹`.
- The Library's form. On a stage `E` the spectral local-field structure
  (`FiniteExtension.normedField`, `valuativeRel`, `isLocalField`) has integer ring the Library's
  `extensionIntegers K E` (`spectralFiniteExtensionIntegerEquiv`), and `𝒪[K]` is `baseIntegers K`
  (`localNormedField_integer`). Transporting the maximal-ideal equality of `ArithmeticUnramified`
  along these identifications gives ramification index one, i.e. NYLL's class. NYLL's residue action
  of the Artin symbol of an element of order one, carried to `ResidueField (extensionIntegers K E)`,
  is `y ↦ y ^ q` (the residue fields of `K` have the same order, `localResidueEquiv`); the Library's
  residue action of a Galois group of an unramified stage is injective
  (`finiteUnramified_residueHom_injective`), so the symbol is `finiteUnramifiedFrobenius`. For general
  `x`, NYLL's Frobenius is the symbol of the Library's uniformizer `localUniformizer K` (order one),
  hence the Library's Frobenius, and the NYLL form gives the power.

## Declarations used

- From the NYLL copy (`…/LocalReciprocity/UniverseFrobenius.lean`,
  `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/{FiniteUnramified, UnramifiedFrobenius,
  ValuationExactSequence}.lean`, `…/LocalReciprocity/UnramifiedComparison.lean`):
  `abelianLocalArtinMonoidHom_eq_frobenius_zpow`, `abelianLocalArtinMap_inverseUniformizer_residue_pow`,
  `IsUnramifiedValuedExtension`, `arithmeticFrobeniusOfUnramifiedValuation`, `valuationMap`, and the
  instances `finiteGaloisLocalField_integerRing_moduleFinite`,
  `finiteGaloisLocalField_integerRing_isIntegralClosure`.
- From the Library: `ArithmeticUnramified` (`Galois/Local/SeparableUnramifiedStatement.lean`),
  `finiteUnramifiedFrobenius`, `finiteUnramifiedFrobenius_residue`,
  `finiteUnramifiedFrobenius_generates`, `finiteUnramified_residueHom_injective`
  (`ClassFieldTheory/Local/FiniteUnramifiedFrobenius.lean`), `spectralFiniteExtensionIntegerEquiv`
  (`FiniteUnramifiedLocalField.lean`), `normalizedUnitOrder`, `localUniformizer`
  (`LocalFieldOrder.lean`), `residueHom`, `integerAut` (`Galois/Local/SpectralDefinitions.lean`),
  `LocalGalois.localNormedField`, `localNormedField_integer`, `localResidueEquiv`
  (`Galois/Local/AbsoluteDefinitions.lean`), `FiniteExtension` (`LocalField/FiniteExtension.lean`).

## Sources

- J.-P. Serre, *Local Fields*, chapter XIII, §4, Proposition 13: for `L/K` unramified,
  `(x, L/K) = F^{v(x)}` with `F` the canonical generator, p. 197; for a finite residue field the
  canonical generator is the Frobenius substitution `x ↦ x^q` (chapter XIII, §2, example a), p. 191).
- J. S. Milne, *Class Field Theory* (version 4.03), chapter I, §1, Theorem 1.1 (a) and 1.8, pp. 20
  and 22–23.
