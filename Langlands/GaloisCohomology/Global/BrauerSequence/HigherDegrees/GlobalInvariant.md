# The global invariant on idèle-class cohomology, and lifting idèle classes to idèles

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/GlobalInvariant.lean`, namespace
`Langlands.GaloisCohomology`.

* `brauerInvariantFamily_relativeImages`, `brauerTotalIdeleInvariant`: the relative images of the
  local family `brauerInvariantFamily` and its total idèle invariant (sum of the local invariants).
* `ideleClassInvariant`: **the global invariant** `inv_{E/F} : H²(Gal(E/F), C_E) → ℚ/ℤ` of the
  Library (`assembledIdeleClassInvariantMaps`, built as in the proof of `globalInvariantStatement`);
  `ideleClassInvariant_images`: injective with image `(1/[E:F])ℤ/ℤ`;
  `ideleClassInvariant_inflation`: invariant under inflation;
  `ideleClassInvariant_ideleQuotient`: on the image of `H²(Gal(E/F), J_E)` it is the total local
  invariant.
* `denominatorSubgroup_le_of_dvd`: `(1/m)ℤ/ℤ ⊆ (1/n)ℤ/ℤ` when `m ∣ n`.
* `relativeIdeleClassInflation_mem_range`: **if a finite place `v` of `F` has local degree in `L`
  divisible by `[E : F]`, the inflation to `L` of every class of `H²(Gal(E/F), C_E)` is the image of a
  class of `H²(Gal(L/F), J_L)`** (the local section at `v` of the local class with the same
  invariant).

## Complete types

```lean
Langlands.GaloisCohomology.brauerInvariantFamily_relativeImages : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
  (Langlands.GaloisCohomology.brauerInvariantFamily p).RelativeImages
Langlands.GaloisCohomology.brauerTotalIdeleInvariant : Langlands.ClassFieldTheory.Global.IdeleInvariantMaps
Langlands.GaloisCohomology.ideleClassInvariant : Langlands.ClassFieldTheory.Global.FundamentalClass.GlobalInvariantMaps
Langlands.GaloisCohomology.ideleClassInvariant_images : Langlands.ClassFieldTheory.Global.FundamentalClass.InvariantImages
  Langlands.GaloisCohomology.ideleClassInvariant
Langlands.GaloisCohomology.ideleClassInvariant_inflation : Langlands.ClassFieldTheory.Global.FundamentalClass.InvariantInflationOnClasses
  Langlands.GaloisCohomology.ideleClassInvariant
Langlands.GaloisCohomology.ideleClassInvariant_ideleQuotient : ∀ (F E : Type u_1) [inst : Field F] [inst_1 : Field E]
  [inst_2 : NumberField F] [inst_3 : NumberField E] [inst_4 : Algebra F E] [inst_5 : IsGalois F E]
  (a : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E 2)),
  (Langlands.GaloisCohomology.ideleClassInvariant F E)
      ((CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.ideleQuotientCohomologyMap F E 2)) a) =
    (Langlands.GaloisCohomology.brauerTotalIdeleInvariant F E) a
@Langlands.GaloisCohomology.denominatorSubgroup_le_of_dvd : ∀ {m n : ℕ},
  m ∣ n →
    Langlands.ClassFieldTheory.Local.denominatorSubgroup m ≤ Langlands.ClassFieldTheory.Local.denominatorSubgroup n
@Langlands.GaloisCohomology.relativeIdeleClassInflation_mem_range : ∀ {F E L : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : Field L] [inst_3 : NumberField F] [inst_4 : NumberField E] [inst_5 : NumberField L]
  [inst_6 : Algebra F E] [inst_7 : Algebra F L] [inst_8 : Algebra E L] [inst_9 : IsScalarTower F E L]
  [inst_10 : IsGalois F E] [IsGalois F L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
  Module.finrank F E ∣
      Module.finrank (Langlands.Global.CompletionPadic.padicField v).Carrier
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion L ↑(Langlands.Global.AdelicFunctoriality.placeAbove L v)) →
    ∀ (c : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleClassCohomology F E 2)),
      ∃ (a : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F L 2)),
        (CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.ideleQuotientCohomologyMap F L 2)) a =
          (CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.relativeIdeleClassInflation F E L 2))
            c
```

## Outline of the proofs

The invariant and its three properties are the Library's `assembledIdeleClassInvariantMaps` and its
lemmas `_images`, `_inflation`, `_apply_quotient`, with the inputs of `globalInvariantStatement`
(`ideleClassH1Vanishing`, `ideleClassGaloisDescent`, `ideleClassH2OrderBound`,
`cyclicPrimePowerLocalDegreeStatement`, the local laws of `brauerInvariantFamily`). For the lift: the
invariant of `c` lies in `(1/[E:F])ℤ/ℤ ⊆ (1/[L_w:F_v])ℤ/ℤ`, which is the image of the local invariant
(`RelativeImages`); the local section of the corresponding local class `z`
(`ideleLocalSection`) has total invariant `inv_loc(z)` (`totalIdeleInvariantMaps_ideleLocalSection`),
equal to the invariant of the inflation of `c`, and the global invariant is injective.

## Declarations

`brauerInvariantFamily_relativeImages`, `brauerTotalIdeleInvariant`, `ideleClassInvariant`, `ideleClassInvariant_images`, `ideleClassInvariant_inflation`, `ideleClassInvariant_ideleQuotient`, `denominatorSubgroup_le_of_dvd`, `relativeIdeleClassInflation_mem_range`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013), Chapter VIII, §1, Proposition (8.1.20), p. 439 (`H²(k, I) → H²(k, C)` is
  surjective, in the limit), Theorem (8.1.22), p. 441 (the invariant maps of the class formation).
- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §11.2, p. 196 (`H²(L/K, C_L)` is cyclic of order `n`
  with invariant `1/n` on its generator; the image of the idèles under the invariant is
  `(1/n₀)ℤ/ℤ`, `n₀` the least common multiple of the local degrees).
