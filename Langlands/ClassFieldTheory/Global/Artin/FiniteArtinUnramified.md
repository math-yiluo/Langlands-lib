# The arithmetic Artin map on local units and ramification

Module `Langlands.ClassFieldTheory.Global.Artin.FiniteArtinUnramified`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library; it reads the NYLL
library's local–global compatibility and its theorems on conductors (the copy under `Nyll/`)
for the arithmetic Artin map `arithmeticFiniteArtin K L` of `FiniteArtin`.

For a finite abelian extension of number fields `L / K` and a finite place `v` of `K`:

- the arithmetic Artin map kills the one-place idèle class of `a ∈ K_v^×` exactly when `a` is a
  norm from the `K_v`-algebra `K_v ⊗[K] L` (the local norm group, without choosing a prime of `L`
  above `v`);
- **the unit criterion**: if the arithmetic Artin map kills the local units at `v`, every prime of
  `L` above `v` is unramified over `K`; with `FiniteArtinNormalization` this is an equivalence.

## Main declarations

Throughout, `K : Type u`, `L : Type v`, `[Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]`; `FinitePlace` is
`Langlands.Global.FinitePlace`, `𝓞` is `NumberField.RingOfIntegers`, and `⊗[K]` is
`TensorProduct K`.

```lean
theorem arithmeticFiniteArtin_finiteClassInclusion_eq_one_iff
    (v : FinitePlace K) (a : (FiniteCompletion K v)ˣ) :
    arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1 ↔
      a ∈ (Units.map (Algebra.norm (FiniteCompletion K v)) :
        (FiniteCompletion K v ⊗[K] L)ˣ →* (FiniteCompletion K v)ˣ).range

theorem isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one
    (v : FinitePlace K)
    (h : ∀ a : (FiniteCompletion K v)ˣ, a ∈ (v.adicCompletionIntegers K).units →
      arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1)
    (w : FinitePlace L) (hw : w.asIdeal.LiesOver v.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal

theorem arithmeticFiniteArtin_finiteClassInclusion_units_eq_one_iff (v : FinitePlace K) :
    (∀ a : (FiniteCompletion K v)ˣ, a ∈ (v.adicCompletionIntegers K).units →
      arithmeticFiniteArtin K L (finiteClassInclusion K v a) = 1) ↔
      ∀ w : FinitePlace L, w.asIdeal.LiesOver v.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
```

`(v.adicCompletionIntegers K).units` is the group of units of the valuation ring of
`FiniteCompletion K v = v.adicCompletion K`; it is by definition the group
`(Submonoid.ofClass (v.adicCompletionIntegers K)).units` of the published statements.

## Proofs

- *Kernel at `v`.* `arithmeticFiniteArtin_finiteClassInclusion` (`FiniteArtin`) gives NYLL's
  chosen local map in arithmetic normalization, which is the inverse of NYLL's chosen local Artin
  map at `v` (`arithmeticChosenFinitePlaceArtinMonoidHom_apply`). Its kernel is the norm group
  of the completion of `L` at NYLL's chosen prime above `v`
  (`chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm`), and NYLL identifies that group
  with the image of the norm of `K_v ⊗[K] L` (`finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`;
  NYLL's `localTensorNorm v` is `Units.map (Algebra.norm (v.adicCompletion K))` by definition).
  These are the two ingredients of NYLL's `exists_finiteAbelianGlobalArtin_finitePlaceNormKernel`
  (`FinitePlaceLocalGlobalNormKernel`), here applied to the named map instead of an existential one.
- *Unit criterion.* The hypothesis puts the local units at `v` into the local norm group. NYLL's
  full norm conductor of `L / K` is an abelian conductor (`normFullConductor_isAbelianConductor`).
  For an abelian conductor `c`, `c.finitePart v ≤ n` exactly when the `n`-th higher unit group
  lies in the local norm group (`IsAbelianConductor.finiteExponent_le_iff_higherUnit_le_tensorNorm`);
  at `n = 0` the higher unit group is the group of units (`rayLocalHigherUnitGroup_zero`). So
  `c.finitePart v = 0`, and then every prime above `v` is unramified
  (`IsAbelianConductor.finiteExponent_eq_zero_iff_unramified`).
- *Equivalence.* The converse is `arithmeticFiniteArtin_finiteClassInclusion_of_unit`
  (`FiniteArtinNormalization`), applied at a prime above `v` (`exists_liesOver`,
  `ArtinUniqueness`).

## Declarations used

- From the NYLL copy: `GlobalClassFieldTheory.Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply`
  (`Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean`);
  `GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm`
  (`…/Reciprocity/LocalGlobalArtinCompatibility/Factorization.lean`);
  `finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`
  (`…/AlgebraicNumberTheory/Idele/Relative/FinitePlaceTensorNorm.lean`); `localTensorNorm`
  (`…/AlgebraicNumberTheory/Idele/Extension/LocalComponent.lean`);
  `ClassFieldTheory.normFullConductor_isAbelianConductor`
  (`…/GlobalClassFieldTheory/GlobalClassFields/PublicRayClassComparison.lean`);
  `ClassFieldTheory.IsAbelianConductor.finiteExponent_le_iff_higherUnit_le_tensorNorm`
  (`…/Theorems/ConductorsAndRayClassFields/AbelianConductorFiniteNormCriterion.lean`);
  `ClassFieldTheory.IsAbelianConductor.finiteExponent_eq_zero_iff_unramified`
  (`…/Theorems/ConductorsAndRayClassFields/AbelianConductorFiniteUnramified.lean`);
  `ClassFieldTheory.rayLocalHigherUnitGroup_zero`
  (`…/Theorems/ConductorsAndRayClassFields/RayLocalHigherUnitZero.lean`).
- From the Library: `arithmeticFiniteArtin`, `arithmeticFiniteArtin_finiteClassInclusion`
  (`FiniteArtin`); `arithmeticFiniteArtin_finiteClassInclusion_of_unit`
  (`FiniteArtinNormalization`); `exists_liesOver` (`ArtinUniqueness`); `FinitePlace`,
  `FiniteCompletion`, `finiteClassInclusion` (`Langlands/Global/Adelic.lean`).
- From Mathlib: `Algebra.norm`, `Units.map`, `TensorProduct`, `Algebra.IsUnramifiedAt`.

## Sources

Neukirch, *Algebraic Number Theory* (Springer, 1999): Chapter VI, Corollary (5.8), p. 394
(`N_{L|K} C_L ∩ K_𝔭^* = N_𝔭 L_𝔓^*`: the kernel of the global norm residue symbol on `K_𝔭^*` is
the local norm group), Definition (6.4) and Proposition (6.5), p. 397 (the conductor of `L|K` is
the product of the local conductors), Corollary (6.6), p. 398 (`𝔭` is ramified in `L` if and only
if `𝔭` divides the conductor); Chapter V, Definition (1.6) and Proposition (1.7), p. 323 (the local
conductor is `𝔭^n` for the least `n` with `U^{(n)} ⊆ N L_𝔓^*`, and `L_𝔓|K_𝔭` is unramified if and
only if it is `1`). The proof here follows the same route: kernel at `v` = local norm group;
units in it = local conductor exponent `0` = unramified. Neukirch states (5.8) with the norm group
of one completion `L_𝔓`; NYLL's form with `K_v ⊗[K] L` has the same image, since `K_v ⊗[K] L` is
a product of copies of `L_𝔓` for an abelian `L / K`.
