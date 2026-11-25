# The local Artin map of a finite abelian extension of a nonarchimedean local field

Module `Langlands.ClassFieldTheory.Local.Artin.FiniteArtin`, name space
`Langlands.ClassFieldTheory.Local.Artin`. This file belongs to the Library; it states the local
Artin map of the NYLL library (the copy under `Nyll/`) for a finite abelian extension of a
nonarchimedean local field of any characteristic (Mathlib's `IsNonarchimedeanLocalField`), in the
Library's vocabulary.

For such a field `K` and a finite abelian extension `L / K`:

- `geometricFiniteArtin K L : Kˣ →ₜ* Gal(L/K)` is NYLL's map
  `LocalClassFieldTheory.Universe.abelianLocalArtinMap K L`, in the **geometric** normalization: a
  uniformizer goes to the inverse of the arithmetic Frobenius on unramified extensions (NYLL's
  normalized valuation `valuationMap` is minus the order, `FiniteArtinNormalization`).
- `arithmeticFiniteArtin K L : Kˣ →ₜ* Gal(L/K)` is the geometric map of the inverse unit, in the
  **arithmetic** normalization: a uniformizer goes to the arithmetic Frobenius
  (`arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow`). This is the normalization of Serre,
  Neukirch and Milne, and of the Library's local invariant.

Both maps are onto, with kernel the norm group `N_{L/K}(Lˣ)` (the Library's
`LocalClassField.normSubgroup K L`, which is NYLL's `ClassFieldTheory.fieldNormSubgroup K L` by
definition); both are compatible with restriction along every tower `K ⊆ E ⊆ L` of finite abelian
extensions (the fields in independent universes, the embeddings arbitrary), and with the norm of a
finite separable extension of the base. On the Library's finite abelian extensions inside
`AlgebraicClosure K` (`LocalClassField.FiniteAbelianExtension K`), the arithmetic maps form a family
`arithmeticFiniteArtinFamily K` satisfying the Library's unnormalized relation
`LocalClassField.FiniteArtinSystemRelation` (onto, kernel the norm group, compatible with
restriction): an inhabitant of the relations of `Langlands/ClassFieldTheory/Local/FiniteArtin.lean`.

## Main declarations

Throughout, `K : Type u`, `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, and `L : Type v`, `[Field L] [Algebra K L] [FiniteDimensional K L]
[IsAbelianGalois K L]`.

```lean
def unitsInv (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] : Kˣ →ₜ* Kˣ

def geometricFiniteArtin : Kˣ →ₜ* Gal(L/K) :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMap K L

def arithmeticFiniteArtin : Kˣ →ₜ* Gal(L/K) :=
  (geometricFiniteArtin K L).comp (unitsInv K)

theorem arithmeticFiniteArtin_apply (a : Kˣ) :
    arithmeticFiniteArtin K L a = geometricFiniteArtin K L a⁻¹
theorem arithmeticFiniteArtin_eq_inv (a : Kˣ) :
    arithmeticFiniteArtin K L a = (geometricFiniteArtin K L a)⁻¹
theorem geometricFiniteArtin_eq_inv (a : Kˣ) :
    geometricFiniteArtin K L a = (arithmeticFiniteArtin K L a)⁻¹

theorem geometricFiniteArtin_surjective : Function.Surjective (geometricFiniteArtin K L)
theorem arithmeticFiniteArtin_surjective : Function.Surjective (arithmeticFiniteArtin K L)
theorem geometricFiniteArtin_ker :
    (geometricFiniteArtin K L).toMonoidHom.ker = LocalClassField.normSubgroup K L
theorem arithmeticFiniteArtin_ker :
    (arithmeticFiniteArtin K L).toMonoidHom.ker = LocalClassField.normSubgroup K L
theorem arithmeticFiniteArtin_eq_one_iff (a : Kˣ) :
    arithmeticFiniteArtin K L a = 1 ↔ a ∈ LocalClassField.normSubgroup K L

-- E : Type v, L : Type w, [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L],
-- both finite abelian over K
theorem restrictNormalHom_geometricFiniteArtin (a : Kˣ) :
    AlgEquiv.restrictNormalHom E (geometricFiniteArtin K L a) = geometricFiniteArtin K E a
theorem restrictNormalHom_arithmeticFiniteArtin (a : Kˣ) :
    AlgEquiv.restrictNormalHom E (arithmeticFiniteArtin K L a) = arithmeticFiniteArtin K E a

-- K' a local field, finite separable over K with
-- [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation K')];
-- L finite abelian over K, L' finite abelian over K', [IsScalarTower K K' L'] [IsScalarTower K L L']
theorem restrictNormalHom_arithmeticFiniteArtin_normUnits (a : K'ˣ) :
    AlgEquiv.restrictNormalHom L
        (AlgEquiv.restrictScalarsHom K (arithmeticFiniteArtin K' L' a)) =
      arithmeticFiniteArtin K L (LocalClassField.normUnits K K' a)

instance finiteAbelianExtension_isAbelianGalois (L : LocalClassField.FiniteAbelianExtension K) :
    IsAbelianGalois K L.field
def arithmeticFiniteArtinFamily : LocalClassField.FiniteArtinFamily K :=
  fun L => arithmeticFiniteArtin K L.field
theorem finiteArtinSystemRelation_arithmeticFiniteArtinFamily :
    LocalClassField.FiniteArtinSystemRelation (arithmeticFiniteArtinFamily K)
```

## Proofs

Surjectivity and the kernel are NYLL's `abelianLocalArtinMap_surjective` and
`abelianLocalArtinMap_ker`; for the arithmetic map, `a` is in the kernel exactly when `a⁻¹` is.
Compatibility with restriction is NYLL's `abelianLocalArtinMonoidHom_restrict_tower` (any tower, any
universes), the norm compatibility NYLL's `abelianLocalArtinMonoidHom_norm_restriction`, applied to
the inverse unit for the arithmetic maps (`Units.map` commutes with inversion). The family relation
collects these three facts on the Library's finite abelian extensions.

## Declarations used

- From the NYLL copy
  (`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseArtin.lean`,
  `UniverseNaturality.lean`): `LocalClassFieldTheory.Universe.abelianLocalArtinMap`,
  `abelianLocalArtinMap_surjective`, `abelianLocalArtinMap_ker`,
  `abelianLocalArtinMonoidHom_restrict_tower`, `abelianLocalArtinMonoidHom_norm_restriction`.
- From the Library (`Langlands/ClassFieldTheory/Local/FiniteArtin.lean`, `Norms.lean`, `Galois.lean`):
  `LocalClassField.normSubgroup`, `normUnits`, `FiniteAbelianExtension`, `FiniteArtinFamily`,
  `FiniteArtinSystemRelation`, `FiniteAbelianExtension.restrictionOfLE`.

## Sources

- J.-P. Serre, *Local Fields*, chapter XIII, §4, Proposition 12 (compatibility of the reciprocity
  map with restriction), p. 197; chapter XI, §3 (the reciprocity isomorphism of a class formation,
  onto with kernel the norm group), p. 169.
- J. Neukirch, *Algebraic Number Theory*, chapter V, §1, Theorem (1.3) (local reciprocity law) and
  the norm residue symbol `( , L|K)` defined after it, pp. 320–321.
- J. S. Milne, *Class Field Theory* (version 4.03), chapter I, §1, Theorem 1.1 (local reciprocity
  law), p. 20.

All three normalize arithmetically (`arithmeticFiniteArtin`); NYLL's map is the inverse.
