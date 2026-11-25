# The local Artin homomorphism and the norm group

Module `Langlands.ClassFieldTheory.Local.Artin.NormSubgroup`, namespace
`Langlands.ClassFieldTheory.Local.Artin`. This file belongs to the Library; it states the local
reciprocity law of the NYLL library (the copy under `Nyll/`) for a finite abelian extension `L / K` of
a nonarchimedean local field `K` of any characteristic (Mathlib's `IsNonarchimedeanLocalField`,
`K : Type u`, `L : Type v`), with the norm group `DiscreteValuationField.fieldNormSubgroup K L` of the
valued-field part of the copy (the image of `Algebra.norm K` on `Lˣ`):

- `abelianArtinHom K L : Kˣ →* Gal(L/K)` is NYLL's
  `LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom K L`, in the geometric normalization (a
  uniformizer goes to the inverse of the arithmetic Frobenius on unramified extensions); its continuous
  form is `geometricFiniteArtin K L` of `Langlands.ClassFieldTheory.Local.Artin.FiniteArtin`;
- `abelianArtinHom_surjective`: it is onto;
- `abelianArtinHom_ker`: its kernel is the norm group `N_{L/K}(Lˣ)`.

So `Gal(L/K) ≅ Kˣ / N_{L/K}(Lˣ)`; the module `Langlands.GaloisCohomology.Local.Duality.NormCharacters`
derives from these the reciprocity isomorphism and the norm index `[Kˣ : N(Lˣ)] = [L : K]`.

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom.{u, v} (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L] : Kˣ →* Gal(L/K)
Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom_surjective.{u, v} (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L] : Function.Surjective ⇑(Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom K L)
Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom_ker.{u, v} (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L] :
  (Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom K L).ker =
    LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup K L
```

## Proofs

The three declarations are NYLL's `abelianLocalArtinMonoidHom`, `abelianLocalArtinMonoidHom_surjective`
and `abelianLocalArtinMonoidHom_ker`; NYLL's kernel `LocalFieldTheory.localNormSubgroup K L` is
`fieldNormSubgroup K L` by definition.

## Declarations

`abelianArtinHom`, `abelianArtinHom_surjective`, `abelianArtinHom_ker`.

## Declarations used

From the NYLL copy (`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseArtin.lean`):
`LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom`, `abelianLocalArtinMonoidHom_surjective`,
`abelianLocalArtinMonoidHom_ker`; from its valued-field part
(`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/FieldNorm.lean`):
`DiscreteValuationField.fieldNormSubgroup`.

## Sources

- J. Neukirch, *Algebraic Number Theory* (Springer 1999), chapter V, §1, Theorem (1.3) (local
  reciprocity law: `G(L|K)^ab ≅ K*/N_{L|K}L*` for a finite Galois extension of local fields), p. 320,
  and the norm residue symbol `( , L|K) : K* → G(L|K)^ab` obtained by inverting it, p. 321. Neukirch
  works with local fields with finite residue field and the arithmetic normalization; NYLL's map is the
  inverse of the norm residue symbol (geometric normalization).
