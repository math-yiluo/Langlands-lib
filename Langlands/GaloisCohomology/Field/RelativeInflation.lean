import Langlands.Algebra.BrauerComparison.SeparableCohomology
import Langlands.Cohomology.Profinite.Comparison.ContinuousOrdinary
import Langlands.Cohomology.Profinite.Comparison.TwoCocycles
import Langlands.GaloisCohomology.Field.Brauer
import Langlands.GaloisCohomology.Field.FiniteLevel

/-!
# The Library's inflation from a finite level, on cocycles of the cochain model

The Library computes its local invariant on *relative* classes: Mathlib's `groupCohomology` of a
finite Galois group `Gal(L/K)` with coefficients `Lˣ` (`relativeCohomology K L n`), carried into
continuous cohomology of `Gal(S/K)` by `BrauerComparison.relativeToContinuous K L S n` (the inverse
of the Library's comparison `continuousToRelativeEquiv` followed by continuous inflation). This file
describes that map in the cochain model of `Langlands.ProfiniteCohomology`:

* `unitsModuleContinuousEquiv_symm_relativeToContinuous`: read through
  `unitsModuleContinuousEquiv K S n`, it is `isoGroupCohomology⁻¹` (a relative class as a class of
  locally constant cochains of the discrete group `Gal(L/K)`) followed by the foundations' map along
  restriction `Gal(S/K) → Gal(L/K)` and the inclusion `Lˣ → Sˣ`;
* `exists_cocycle_relativeToContinuous_H2π`: on a Mathlib 2-cocycle `c`, the result is the class of
  the locally constant cocycle `(g, h) ↦ c (g|_L, h|_L)`;
* `unitsModuleContinuousEquiv_unitsInflation`: for an intermediate field `E` of `S` it is the
  foundations' explicit inflation `unitsInflation E n`.

The proofs rest on `isoContinuousCohomology_hom_comp_continuousToOrdinary` (the foundations' and
the Library's comparisons with continuous cohomology compose to the inclusion of cochains) and the
naturality `isoContinuousCohomology_naturality`.
-/

noncomputable section

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology ClassFieldTheory.Local BrauerComparison

universe u

section Tower

variable (K L S : Type u) [Field K] [Field L] [Field S] [Algebra K L] [Algebra K S] [Algebra L S]
  [IsScalarTower K L S] [Normal K L] [FiniteDimensional K L] [IsGalois K S]

/-- The underlying representation of the Library's discrete units module of a finite extension is
smooth. -/
instance isSmoothRep_unitsModule_of_finite : IsSmoothRep (unitsModule K L) :=
  inferInstanceAs (IsSmoothRep (underlyingRep (discreteUnitsRepresentation K L)))

/-- The foundations' map along the restriction `Gal(S/K) → Gal(L/K)` and the inclusion `Lˣ → Sˣ`:
inflation from the finite normal level `L` in the cochain model. -/
abbrev unitsTowerMap (n : ℕ) : cohomology (unitsModule K L) n ⟶ cohomology (unitsModule K S) n :=
  map (normalKrullRestriction K L S) (underlyingHom _ (continuousUnitInflationCoefficients K L S)) n

/-- The Library's `relativeToContinuous K L S n`, read in the cochain model, is `isoGroupCohomology⁻¹`
followed by the foundations' inflation `unitsTowerMap K L S n`. -/
theorem unitsModuleContinuousEquiv_symm_relativeToContinuous (n : ℕ)
    (x : relativeCohomology K L n) :
    (unitsModuleContinuousEquiv K S n).symm (relativeToContinuous K L S n x) =
      (unitsTowerMap K L S n).hom ((isoGroupCohomology (unitsModule K L) n).inv.hom x) := by
  rw [LinearEquiv.symm_apply_eq]
  have h1 : (continuousToRelativeEquiv K L n).symm x =
      (isoContinuousCohomology (discreteUnitsRepresentation K L) n).hom.hom
        ((isoGroupCohomology (unitsModule K L) n).inv.hom x) :=
    isoContinuousCohomology_hom_continuousToOrdinary_inv (discreteUnitsRepresentation K L) n x
  have h2 := congrArg (fun f => f.hom ((isoGroupCohomology (unitsModule K L) n).inv.hom x))
    (isoContinuousCohomology_naturality (normalKrullRestriction K L S)
      (continuousUnitInflationCoefficients K L S) n)
  change relativeToContinuous K L S n x =
    (isoContinuousCohomology (discreteUnitsRepresentation K S) n).hom.hom
      ((unitsTowerMap K L S n).hom ((isoGroupCohomology (unitsModule K L) n).inv.hom x))
  refine Eq.trans ?_ h2.symm
  change continuousUnitInflation K L S n ((continuousToRelativeEquiv K L n).symm x) = _
  rw [h1]
  rfl

/-- On a Mathlib 2-cocycle `c` of `Gal(L/K)` with values in `Lˣ`, the Library's inflation, read in
the cochain model, is the class of the locally constant cocycle `(g, h) ↦ c (g|_L, h|_L)`. -/
theorem exists_cocycle_relativeToContinuous_H2π
    (c : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    ∃ w : cocycles (unitsModule K S) 2,
      cohomologyπ (unitsModule K S) 2 w =
        (unitsModuleContinuousEquiv K S 2).symm
          (relativeToContinuous K L S 2 (groupCohomology.H2π (unitsRepresentation K L) c)) ∧
      ∀ v : Fin 2 → Gal(S/K), cochainOf (unitsModule K S) (cocycleι (unitsModule K S) 2 w) v =
        unitInclusion L S (c (AlgEquiv.restrictNormalHom L (v 0),
          AlgEquiv.restrictNormalHom L (v 1))) := by
  let A := unitsModule K L
  have hc : IsLocallyConstant fun v : Fin 2 → Gal(L/K) => c (v 0, v 1) :=
    IsLocallyConstant.of_discrete _
  let z : cocycles A 2 := cocyclesOfCocycles₂ A c hc
  have hz : cochainOf A (cocycleι A 2 z) = fun v => c (v 0, v 1) :=
    cochainOf_cocycleι_cocyclesOfCocycles₂ A c hc
  have hπ : (isoGroupCohomology A 2).hom.hom (cohomologyπ A 2 z) =
      groupCohomology.H2π (unitsRepresentation K L) c := by
    rw [isoGroupCohomology_hom]
    exact toGroupCohomology_cohomologyπ_cocyclesOfCocycles₂ A c hc
  refine ⟨cocyclesMap (normalKrullRestriction K L S)
    (underlyingHom _ (continuousUnitInflationCoefficients K L S)) 2 z, ?_, fun v => ?_⟩
  · rw [unitsModuleContinuousEquiv_symm_relativeToContinuous, ← hπ, Iso.hom_inv_id_apply]
    exact (map_cohomologyπ _ _ z).symm
  · have e := congrFun (cochainOf_cocycleι_cocyclesMap (normalKrullRestriction K L S)
      (underlyingHom _ (continuousUnitInflationCoefficients K L S)) z) v
    refine e.trans ?_
    have hz' := congrFun hz (⇑(normalKrullRestriction K L S) ∘ v)
    exact congrArg (underlyingHom (normalKrullRestriction K L S)
      (continuousUnitInflationCoefficients K L S)).hom hz'

end Tower

section IntermediateField

variable {K S : Type u} [Field K] [Field S] [Algebra K S] [IsGalois K S]
  (E : IntermediateField K S) [FiniteDimensional K E] [Normal K E]

/-- For an intermediate field `E` of `S`, the Library's `relativeToContinuous K E S n`, read in the
cochain model, is the foundations' explicit inflation `unitsInflation E n`. -/
theorem unitsModuleContinuousEquiv_unitsInflation (n : ℕ) (x : relativeCohomology K E n) :
    unitsModuleContinuousEquiv K S n ((unitsInflation E n).hom x) =
      relativeToContinuous K E S n x := by
  rw [← LinearEquiv.eq_symm_apply, unitsModuleContinuousEquiv_symm_relativeToContinuous]
  have hcochain : cochainsι (unitsModule K E) ≫ unitsInflationCochains E =
      cochainsMap (normalKrullRestriction K E S)
        (underlyingHom _ (continuousUnitInflationCoefficients K E S)) := by
    ext m : 1
    rw [← cancel_mono ((cochainsι (unitsModule K S)).f m)]
    have h1 := congrArg (fun φ => φ.f m) (unitsInflationCochains_comp_cochainsι E)
    have h2 := congrArg (fun φ => φ.f m) (cochainsMap_comp_cochainsι (normalKrullRestriction K E S)
      (underlyingHom _ (continuousUnitInflationCoefficients K E S)))
    simp only [HomologicalComplex.comp_f] at h1 h2
    rw [HomologicalComplex.comp_f, Category.assoc, h1]
    exact h2.symm
  have key : (toGroupCohomology (unitsModule K E) n ≫ unitsInflation E n :
      cohomology (unitsModule K E) n ⟶ cohomology (unitsModule K S) n) = unitsTowerMap K E S n := by
    have h := congrArg (fun f => HomologicalComplex.homologyMap f n) hcochain
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact h
  obtain ⟨y, rfl⟩ := (isoGroupCohomology (unitsModule K E) n).toLinearEquiv.surjective x
  change (unitsInflation E n).hom ((isoGroupCohomology (unitsModule K E) n).hom.hom y) =
    (unitsTowerMap K E S n).hom
      ((isoGroupCohomology (unitsModule K E) n).inv.hom
        ((isoGroupCohomology (unitsModule K E) n).hom.hom y))
  rw [Iso.hom_inv_id_apply, ← key, isoGroupCohomology_hom]
  rfl

end IntermediateField

end Langlands.GaloisCohomology
