# The Library's inflation from a finite level, on cocycles of the cochain model

`Langlands/GaloisCohomology/Field/RelativeInflation.lean`, namespace `Langlands.GaloisCohomology`.

The Library computes its local invariant on *relative* classes: Mathlib's `groupCohomology` of a
finite Galois group `Gal(L/K)` with coefficients `Lˣ` (`ClassFieldTheory.Local.relativeCohomology K L
n`), carried into Mathlib's continuous cohomology of `Gal(S/K)` with coefficients `Sˣ` by
`BrauerComparison.relativeToContinuous K L S n` — the inverse of the Library's comparison
`continuousToRelativeEquiv K L n` (homogeneous continuous cochains of the finite group against
inhomogeneous cochains) followed by continuous inflation along the restriction `Gal(S/K) → Gal(L/K)`
and the inclusion `Lˣ → Sˣ`. This file describes that map in the cochain model of
`Langlands.ProfiniteCohomology`, through the foundations' isomorphism
`unitsModuleContinuousEquiv K S n : cohomology (unitsModule K S) n ≃ continuousUnitCohomology K S n`.

Let `K ⊆ L ⊆ S` be fields with `L / K` finite normal (`L` any field with a `K`-embedding into `S`,
not necessarily a subfield) and `S / K` Galois.

- `unitsModuleContinuousEquiv_symm_relativeToContinuous`: read in the cochain model,
  `relativeToContinuous K L S n` is `isoGroupCohomology⁻¹` (the relative class as a class of
  locally constant cochains of the discrete group `Gal(L/K)`) followed by the foundations' map
  `unitsTowerMap K L S n` along the restriction `Gal(S/K) → Gal(L/K)` and the inclusion `Lˣ → Sˣ`
  (the inflation, in the sense of the compatible pair `G → G/H`, `A^H → A`).
- `exists_cocycle_relativeToContinuous_H2π`: on a Mathlib 2-cocycle `c` of `Gal(L/K)` with values in
  `Lˣ`, the image is the class of the locally constant cocycle `(g, h) ↦ c(g|_L, h|_L)` of
  `Gal(S/K)` with values in `Sˣ`.
- `unitsModuleContinuousEquiv_unitsInflation`: for an intermediate field `E` of `S`, the map is the
  foundations' explicit inflation `unitsInflation E n` (`Field/FiniteLevel.lean`).

## Declarations

`K L S : Type u`, `[Field K] [Field L] [Field S] [Algebra K L] [Algebra K S] [Algebra L S]
[IsScalarTower K L S] [Normal K L] [FiniteDimensional K L] [IsGalois K S]`.

```lean
instance isSmoothRep_unitsModule_of_finite : IsSmoothRep (unitsModule K L)

abbrev unitsTowerMap (n : ℕ) : cohomology (unitsModule K L) n ⟶ cohomology (unitsModule K S) n :=
  map (normalKrullRestriction K L S) (underlyingHom _ (continuousUnitInflationCoefficients K L S)) n

theorem unitsModuleContinuousEquiv_symm_relativeToContinuous (n : ℕ)
    (x : relativeCohomology K L n) :
    (unitsModuleContinuousEquiv K S n).symm (relativeToContinuous K L S n x) =
      (unitsTowerMap K L S n).hom ((isoGroupCohomology (unitsModule K L) n).inv.hom x)

theorem exists_cocycle_relativeToContinuous_H2π
    (c : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    ∃ w : cocycles (unitsModule K S) 2,
      cohomologyπ (unitsModule K S) 2 w =
        (unitsModuleContinuousEquiv K S 2).symm
          (relativeToContinuous K L S 2 (groupCohomology.H2π (unitsRepresentation K L) c)) ∧
      ∀ v : Fin 2 → Gal(S/K), cochainOf (unitsModule K S) (cocycleι (unitsModule K S) 2 w) v =
        unitInclusion L S (c (AlgEquiv.restrictNormalHom L (v 0),
          AlgEquiv.restrictNormalHom L (v 1)))

-- {K S : Type u} [Field K] [Field S] [Algebra K S] [IsGalois K S],
-- E : IntermediateField K S, [FiniteDimensional K E] [Normal K E]
theorem unitsModuleContinuousEquiv_unitsInflation (n : ℕ) (x : relativeCohomology K E n) :
    unitsModuleContinuousEquiv K S n ((unitsInflation E n).hom x) =
      relativeToContinuous K E S n x
```

## Proofs

- By `isoContinuousCohomology_hom_continuousToOrdinary_inv`
  (`Cohomology/Profinite/Comparison/ContinuousOrdinary.lean`), the inverse of the Library's
  comparison for the finite discrete group `Gal(L/K)` is `isoContinuousCohomology ∘ isoGroupCohomology⁻¹`;
  continuous inflation corresponds to the foundations' map by the naturality of the comparison
  (`isoContinuousCohomology_naturality`).
- The cocycle form: the relative class of `c` is the class of `cocyclesOfCocycles₂ c`
  (`Comparison/TwoCocycles.lean`); the foundations' map acts on cocycles by
  `g ↦ f (z (φ ∘ g))` (`map_cohomologyπ`, `cochainOf_cocycleι_cocyclesMap`).
- For an intermediate field, `unitsInflationCochains E` after the inclusion of cochains is Mathlib's
  `cochainsMap` along the restriction and `unitsRestrictHom E`, which is the same map as the one
  along `normalKrullRestriction` and the coefficient inclusion; so `unitsInflation` after
  `toGroupCohomology` is `unitsTowerMap`.

## Source and licence

New file.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, chapter I,
  §5, item 2 (inflation, induced by the compatible pair `G → G/H`, `A^H → A`), p. 47.
- J.-P. Serre, *Local Fields*, chapter XIII, §4, proof of Proposition 13 (the invariant of an
  unramified class is computed on the finite level), pp. 197–198.
