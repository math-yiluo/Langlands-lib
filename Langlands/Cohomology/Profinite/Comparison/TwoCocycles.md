# Two-cocycles of the abstract group in the cochain model

`Langlands/Cohomology/Profinite/Comparison/TwoCocycles.lean`, namespace
`Langlands.ProfiniteCohomology`.

Let `G` be a topological group and `A` a smooth representation of `G` over `k`. A Mathlib 2-cocycle
`c ∈ groupCohomology.cocycles₂ A` (a function `G × G → A` satisfying the cocycle identity of the
abstract group) whose associated cochain `g ↦ c (g₀, g₁)` on `G²` is locally constant is a cocycle of
the cochain model of `Langlands.ProfiniteCohomology` (`cocyclesOfCocycles₂ A c hc`), with that
underlying cochain; and the comparison `toGroupCohomology A 2` with the cohomology of the abstract
group sends its class to Mathlib's class `groupCohomology.H2π A c`. For a discrete group (every
function is locally constant) this says how a class of Mathlib's `H²` is represented in the cochain
model; it is used for the Library's relative classes (`Field/RelativeInflation.lean`) and for the
standard cocycle of the cup product of a character with a unit (`Local/CharacterCup.lean`).

## Declarations

`{k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`,
`A : Rep.{u} k G` (the first theorem needs no topology).

```lean
theorem inhomogeneousCochains_d_two_eq_zero (c : groupCohomology.cocycles₂ A) :
    (inhomogeneousCochains.d A 2).hom (fun v : Fin 2 → G => c (v 0, v 1)) = 0

-- [IsSmoothRep A]
def cocyclesOfCocycles₂ (c : groupCohomology.cocycles₂ A)
    (hc : IsLocallyConstant fun v : Fin 2 → G => c (v 0, v 1)) : cocycles A 2
theorem cochainOf_cocycleι_cocyclesOfCocycles₂ (c : groupCohomology.cocycles₂ A)
    (hc : IsLocallyConstant fun v : Fin 2 → G => c (v 0, v 1)) :
    cochainOf A (cocycleι A 2 (cocyclesOfCocycles₂ A c hc)) = fun v => c (v 0, v 1)
theorem toGroupCohomology_cohomologyπ_cocyclesOfCocycles₂ (c : groupCohomology.cocycles₂ A)
    (hc : IsLocallyConstant fun v : Fin 2 → G => c (v 0, v 1)) :
    (toGroupCohomology A 2).hom (cohomologyπ A 2 (cocyclesOfCocycles₂ A c hc)) =
      groupCohomology.H2π A c
```

## Proofs

Mathlib's `isoCocycles₂` identifies `cocycles₂ A` with the cycles of the inhomogeneous complex in
degree 2, the element `c` going to the cycle with cochain `g ↦ c (g₀, g₁)`
(`isoCocycles₂_inv_comp_iCocycles_apply`); its differential vanishes (`iCycles_d`). The cocycle of
the cochain model is built with `cyclesMk`; its image under the inclusion of complexes has the same
underlying cochain as `isoCocycles₂.inv c`, so the two cycles coincide and so do their classes
(`toGroupCohomology_cohomologyπ`, `H2π = isoCocycles₂.inv ≫ π`).

## Source and licence

New file.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, chapter I,
  §2: inhomogeneous cochains and the inhomogeneous coboundary operators, p. 14.
