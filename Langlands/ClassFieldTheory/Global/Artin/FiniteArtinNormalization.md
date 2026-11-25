# The arithmetic Artin map at every uniformizer and on local units

Module `Langlands.ClassFieldTheory.Global.Artin.FiniteArtinNormalization`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it proves, from
the NYLL library (the copy under `Nyll/`), that the arithmetic Artin map of `FiniteArtin`
satisfies the Library's normalization `Langlands.Global.HasArithmeticArtinNormalization`
(`Langlands/Global/Arithmetic/ClassFieldStatement.lean`).

Let `L / K` be a finite abelian extension of number fields, `v` a finite place of `K` and `w` a
prime of `L` above `v` at which `L / K` is unramified. Then every uniformizer `π` of the
completion `K_v` goes under `arithmeticFiniteArtin K L` to an arithmetic Frobenius at `w`, in
the form `(NumberField.RingOfIntegers.mapAlgHom σ).IsArithFrobAt w.asIdeal`, and every unit of
the valuation ring of `K_v` goes to `1`.

## Main declarations

In all but the first, `K : Type u`, `L : Type v`, `[Field K] [NumberField K] [Field L]
[NumberField L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]`.

```lean
theorem mul_inv_chosenLocalOrderSection_mem_units {K : Type u} [Field K] [NumberField K]
    (v : Langlands.Global.FinitePlace K) (π : (FiniteCompletion K v)ˣ)
    (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    π * (FiniteIdeleGroup.chosenLocalOrderSection v 1)⁻¹ ∈
      (v.adicCompletionIntegers K).units

theorem chosenCentre_isUnramifiedAt (v : Langlands.Global.FinitePlace K)
    (w : Langlands.Global.FinitePlace L) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K)
      (finitePlaceExtensionCentre (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)).asIdeal

theorem arithmeticFiniteArtin_finiteClassInclusion_of_unit (v : Langlands.Global.FinitePlace K)
    (w : Langlands.Global.FinitePlace L) (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (a : (FiniteCompletion K v)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers K).units) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1

theorem arithmeticFiniteArtin_finiteClassInclusion_of_valuation_eq_one
    (v : Langlands.Global.FinitePlace K) (w : Langlands.Global.FinitePlace L)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (a : (FiniteCompletion K v)ˣ) (ha : Valued.v (a : FiniteCompletion K v) = 1) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1

theorem arithmeticFiniteArtin_finiteClassInclusion_eq_arithFrobAt
    (v : Langlands.Global.FinitePlace K) (w : Langlands.Global.FinitePlace L)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (π : (FiniteCompletion K v)ˣ)
    (hπ : Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v π) =
      arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal

theorem arithmeticFiniteArtin_hasArithmeticArtinNormalization :
    HasArithmeticArtinNormalization (arithmeticFiniteArtin K L)
```

Here `HasArithmeticArtinNormalization ρ` is the Library's predicate

```lean
∀ (v : FinitePlace K) (w : FinitePlace L),
  w.asIdeal.LiesOver v.asIdeal →
  Algebra.IsUnramifiedAt (RingOfIntegers K) w.asIdeal →
  ∀ π : (FiniteCompletion K v)ˣ,
    Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
    (RingOfIntegers.mapAlgHom (ρ (finiteClassInclusion K v π))).IsArithFrobAt w.asIdeal
```

## Proofs

NYLL fixes at each finite place `v` an element `s = FiniteIdeleGroup.chosenLocalOrderSection v 1`
of normalized order one (valuation `exp (-1)`), and a prime of `L` above `v` (the centre of its
chosen extension of the absolute value).

- *Uniformizers.* NYLL's local order is `-log` of the valuation and is a homomorphism; an element
  of order `0` is a unit of the valuation ring (`FiniteIdeleGroup.localOrder_eq_zero_iff`). So
  `π s⁻¹` is a unit for every uniformizer `π`.
- *Conjugate primes.* The primes of `𝓞 L` above `v` are conjugate under `L ≃ₐ[K] L`, so they
  have the same ramification index (Mathlib's `Ideal.ramificationIdx_eq_of_isGaloisGroup`); a
  prime of a Dedekind extension with separable residue fields is unramified exactly when its
  ramification index is `1` (`Ideal.ramificationIdx_eq_one_iff`). So NYLL's chosen prime above
  `v` is unramified when `w` is.
- *Units.* At a finite place, the arithmetic Artin map is NYLL's chosen local Artin map in
  arithmetic normalization (`arithmeticFiniteArtin_finiteClassInclusion`); its kernel is the
  chosen local norm group (`chosenFinitePlaceArtinMonoidHom_ker`), which contains the units when
  the chosen prime is unramified (`adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup`
  with `chosenFinitePlaceIsUnramified_of_isUnramifiedAt`). An element of valuation `1` has local
  order `0`, hence is such a unit.
- *Frobenius.* Writing `π = (π s⁻¹) s`, the value at `π` is the value at `s`. NYLL identifies it
  with its prime Artin element (`arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin`)
  and that with Mathlib's arithmetic Frobenius `arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal` at any
  unramified `w` above `v` (`arithmeticPrimeArtin_eq_arithmeticFrobeniusAt`). Mathlib's
  `IsArithFrobAt.arithFrobAt` says that this element is an arithmetic Frobenius for the action of
  `L ≃ₐ[K] L` on `𝓞 L`, which is pointwise the Library's `RingOfIntegers.mapAlgHom` form.

## Declarations used

- From the NYLL copy: `FiniteIdeleGroup.chosenLocalOrderSection`, `localOrder_apply`,
  `localOrder_chosenLocalOrderSection`, `localOrder_eq_zero_iff`
  (`Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/IdealMap.lean`); `chosenFinitePlaceExtension`,
  `finitePlaceExtensionCentre`, `finitePlaceExtensionCentre_liesOver`
  (`…/Idele/NormApproximation/FinitePlaces.lean`, `…/Completion/ExtensionIndex.lean`);
  `chosenFinitePlaceIsUnramified_of_isUnramifiedAt`, `adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup`
  (`…/Completion/UnramifiedComparison/`); `GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_ker`,
  `arithmeticChosenFinitePlaceArtinMonoidHom_apply`;
  `GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin`;
  `ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt`
  (`…/GlobalClassFields/MathlibFrobeniusHilbertComparison.lean`).
- From the Library: `arithmeticFiniteArtin`, `arithmeticFiniteArtin_finiteClassInclusion`
  (`FiniteArtin`); `HasArithmeticArtinNormalization` (`Langlands/Global/Arithmetic/ClassFieldStatement.lean`).
- From Mathlib: `arithFrobAt`, `IsArithFrobAt.arithFrobAt`, `IsGaloisGroup.of_isFractionRing`,
  `Ideal.ramificationIdx_eq_of_isGaloisGroup`, `Ideal.ramificationIdx_eq_one_iff`.

## Sources

Neukirch, *Algebraic Number Theory*, Chapter VI, (5.5) and (5.6) (the global norm residue
symbol and its values at unramified places); Milne, *Class Field Theory*, Chapter V,
Theorem 5.3 (the Artin map sends a uniformizer at an unramified place to the Frobenius).
