# The connecting map of the idèle sequence and inflation

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/Connecting.lean`, namespace
`Langlands.GaloisCohomology`.

The connecting homomorphism of Mathlib's long exact sequence is natural for a change of group
together with a morphism of short exact sequences of representations (`groupCohomology_δ_comp_map` of
the module `Langlands.Cohomology.RestrictedProduct`). Here:

* `ideleCoefficientSequenceInflation F E L`: for number fields `F ⊆ E ⊆ L` with `E / F` normal, the
  inclusions `Eˣ → Lˣ`, `J_E → J_L`, `C_E → C_L` form a morphism from the restricted idèle sequence of
  `Gal(E/F)` to the idèle sequence of `Gal(L/F)`.
* `δ_comp_relativeInflation`, `relativeInflation_δ_apply`: the connecting maps of the idèle sequences
  commute with inflation (`relativeInflation`, `relativeIdeleClassInflation`).
* `unitsInflationOfLE_eq_relativeInflation`: the foundations' inflation `unitsInflationOfLE` between
  two finite levels `E ≤ E'` of a field extension is the Library's `relativeInflation` for the algebra
  `E → E'` given by the inclusion.

## Complete types

```lean
Langlands.GaloisCohomology.ideleCoefficientSequenceInflation : (F E L : Type u_1) →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Field L] →
        [inst_3 : NumberField E] →
          [inst_4 : NumberField L] →
            [inst_5 : Algebra F E] →
              [inst_6 : Algebra F L] →
                [inst_7 : Algebra E L] →
                  [inst_8 : IsScalarTower F E L] →
                    [inst_9 : Normal F E] →
                      (Langlands.ClassFieldTheory.Global.ideleCoefficientSequence F E).map
                          (Rep.resFunctor (AlgEquiv.restrictNormalHom E)) ⟶
                        Langlands.ClassFieldTheory.Global.ideleCoefficientSequence F L
Langlands.GaloisCohomology.δ_comp_relativeInflation : ∀ (F E L : Type u_1) [inst : Field F] [inst_1 : Field E]
  [inst_2 : Field L] [inst_3 : NumberField E] [inst_4 : NumberField L] [inst_5 : Algebra F E] [inst_6 : Algebra F L]
  [inst_7 : Algebra E L] [inst_8 : IsScalarTower F E L] [inst_9 : Normal F E] (i j : ℕ) (hij : i + 1 = j),
  CategoryTheory.CategoryStruct.comp (groupCohomology.δ ⋯ i j hij)
      (Langlands.ClassFieldTheory.Local.relativeInflation F E L j) =
    CategoryTheory.CategoryStruct.comp (Langlands.ClassFieldTheory.Global.relativeIdeleClassInflation F E L i)
      (groupCohomology.δ ⋯ i j hij)
Langlands.GaloisCohomology.relativeInflation_δ_apply : ∀ (F E L : Type u_1) [inst : Field F] [inst_1 : Field E]
  [inst_2 : Field L] [inst_3 : NumberField E] [inst_4 : NumberField L] [inst_5 : Algebra F E] [inst_6 : Algebra F L]
  [inst_7 : Algebra E L] [inst_8 : IsScalarTower F E L] [inst_9 : Normal F E] (i j : ℕ) (hij : i + 1 = j)
  (c : ↑(Langlands.ClassFieldTheory.Global.relativeIdeleClassCohomology F E i)),
  (CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Local.relativeInflation F E L j))
      ((CategoryTheory.ConcreteCategory.hom (groupCohomology.δ ⋯ i j hij)) c) =
    (CategoryTheory.ConcreteCategory.hom (groupCohomology.δ ⋯ i j hij))
      ((CategoryTheory.ConcreteCategory.hom (Langlands.ClassFieldTheory.Global.relativeIdeleClassInflation F E L i)) c)
@Langlands.GaloisCohomology.unitsInflationOfLE_eq_relativeInflation : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : Field Ω] [inst_2 : Algebra K Ω] {E E' : IntermediateField K Ω} (h : E ≤ E') [inst_3 : Normal K ↥E] (n : ℕ),
  Langlands.GaloisCohomology.unitsInflationOfLE h n = Langlands.ClassFieldTheory.Local.relativeInflation K (↥E) (↥E') n
```

## Outline of the proofs

The squares of the idèle morphism commute by `ideleInclusion_diagonal` and by
definition of the idèle-class inclusion. The two inflations between finite levels are maps along the
same restriction homomorphism with the same coefficient function (`groupCohomology.map_congr`).

## Declarations

`ideleCoefficientSequenceInflation`, `δ_comp_relativeInflation`, `relativeInflation_δ_apply`, `unitsInflationOfLE_eq_relativeInflation`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J. T. Tate, *Global Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VII, §11.4, p. 198 (the long exact sequence of
  `0 → Lˣ → J_L → C_L → 0`).
