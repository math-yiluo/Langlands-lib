# The arithmetic Artin map of a finite abelian extension on the Library's idèle classes

Module `Langlands.ClassFieldTheory.Global.Artin.FiniteArtin`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it states the
global Artin map of the NYLL library (the copy under `Nyll/`) for a finite abelian extension of
number fields on the Library's `IdeleClasses K`.

For number fields `K` and `L` with `L / K` finite abelian, `arithmeticFiniteArtin K L` is the
Artin (norm-residue) homomorphism from the idèle classes of `K` onto `Gal(L/K)` in the
**arithmetic** normalization: a uniformizer at a place unramified in `L` goes to the arithmetic
Frobenius (proved in `FiniteArtinNormalization`). NYLL's own global map is geometric; its
arithmetic map, used here, is by definition the inverse of the geometric one.

## Main declarations

Throughout, `K : Type u`, `L : Type v`, `[Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]`.

```lean
def arithmeticFiniteArtin : IdeleClasses K →* (L ≃ₐ[K] L) :=
  (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L).comp
    (nyllIdeleClassEquiv K).symm.toMulEquiv.toMonoidHom

theorem arithmeticFiniteArtin_apply (x : IdeleClasses K) :
    arithmeticFiniteArtin K L x =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom K L
        ((nyllIdeleClassEquiv K).symm x)

theorem arithmeticFiniteArtin_surjective : Function.Surjective (arithmeticFiniteArtin K L)

theorem arithmeticFiniteArtin_continuous : Continuous (arithmeticFiniteArtin K L)

theorem krullTopology_eq_bot : krullTopology K L = ⊥

theorem arithmeticFiniteArtin_continuous_bot :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    Continuous (arithmeticFiniteArtin K L)

def arithmeticFiniteArtinBot :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    IdeleClasses K →ₜ* (L ≃ₐ[K] L)

theorem arithmeticFiniteArtin_ker :
    (arithmeticFiniteArtin K L).ker =
      ((_root_.ideleClassNorm K L).range).map (nyllIdeleClassEquiv K).toMulEquiv.toMonoidHom

theorem arithmeticFiniteArtin_finiteClassInclusion (v : Langlands.Global.FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v x) =
      GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom K L v x
```

`arithmeticFiniteArtin_continuous` is for the Krull topology on `L ≃ₐ[K] L` (Mathlib's
instance), `arithmeticFiniteArtin_continuous_bot` for the discrete topology `⊥`, the form in
which the Library's published statements (`Langlands.Global.FiniteAbelianClassFieldStatement`)
put the Galois group. `krullTopology_eq_bot` (only `[FiniteDimensional K L]` is used) says the
two agree. `arithmeticFiniteArtinBot` is the map as a continuous homomorphism for `⊥`; its
`toMonoidHom` is `arithmeticFiniteArtin K L` by definition.

The kernel is stated with NYLL's idèle-class norm `_root_.ideleClassNorm K L :
_root_.IdeleClassGroup L →* _root_.IdeleClassGroup K`, carried to the Library's group.

## Proofs

Surjectivity, continuity and the kernel are NYLL's
`arithmeticGlobalNormResidueMonoidHom_surjective`, `_continuous` and `_ker` transported along the
homeomorphism `nyllIdeleClassEquiv K`. The Krull topology of a finite extension is discrete
(Mathlib's instance `krullTopology_discreteTopology_of_finiteDimensional`), which gives the `⊥`
forms. At a finite place, NYLL's local–global compatibility
`arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass` together with
`nyllIdeleClassEquiv_symm_finiteClassInclusion` gives the last statement.

## Declarations used

- From the NYLL copy (`Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean`):
  `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom` and its
  `_surjective`, `_continuous`, `_ker`, `_comp_finitePlaceIdeleClass`;
  `arithmeticChosenFinitePlaceArtinMonoidHom`; `ideleClassNorm`
  (`…/AlgebraicNumberTheory/Idele/Extension/IdeleNorm.lean`).
- From the Library: `nyllIdeleClassEquiv`, `nyllIdeleClassEquiv_symm_finiteClassInclusion`
  (`IdeleClassComparison`); `IdeleClasses`, `FinitePlace`, `FiniteCompletion`,
  `finiteClassInclusion` (`Langlands/Global/Adelic.lean`).
- From Mathlib: `krullTopology`, `krullTopology_discreteTopology_of_finiteDimensional`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, (5.5) and (5.6) (the global norm residue
symbol and the reciprocity isomorphism `C_K / N_{L|K} C_L ≅ G(L|K)`); Milne, *Class Field
Theory*, Chapter V, Theorem 5.3; Artin–Tate, *Class Field Theory* (the reciprocity law for idèle
classes).
