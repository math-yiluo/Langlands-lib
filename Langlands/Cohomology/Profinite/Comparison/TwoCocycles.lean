import Langlands.Cohomology.Profinite.Cup.Inflation

/-!
# Two-cocycles of the abstract group in the cochain model

A 2-cocycle `c : G × G → A` of Mathlib's `groupCohomology.cocycles₂ A` (cocycles of the abstract
group `G`) that is locally constant on `G × G` is a cocycle of the cochain model of
`Langlands.ProfiniteCohomology` (`cocyclesOfCocycles₂`), with underlying cochain `g ↦ c (g₀, g₁)`,
and its class is carried by `toGroupCohomology` to Mathlib's class `groupCohomology.H2π A c`
(`toGroupCohomology_cohomologyπ_cocyclesOfCocycles₂`).
-/

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The inhomogeneous differential of a Mathlib 2-cocycle, read on `G²`, vanishes. -/
theorem inhomogeneousCochains_d_two_eq_zero (c : groupCohomology.cocycles₂ A) :
    (inhomogeneousCochains.d A 2).hom (fun v : Fin 2 → G => c (v 0, v 1)) = 0 := by
  have e := (groupCohomology.inhomogeneousCochains A).iCycles_d 2 (2 + 1)
  rw [groupCohomology.inhomogeneousCochains.d_def] at e
  have e2 := congrArg (fun φ => φ.hom ((groupCohomology.isoCocycles₂ A).inv c)) e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at e2
  change (inhomogeneousCochains.d A 2).hom
    (groupCohomology.iCocycles A 2 ((groupCohomology.isoCocycles₂ A).inv c)) = 0 at e2
  rw [groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply] at e2
  convert e2 using 2
  funext v
  rfl

variable [IsSmoothRep A]

/-- A locally constant 2-cocycle of the abstract group, as a cocycle of the cochain model. -/
def cocyclesOfCocycles₂ (c : groupCohomology.cocycles₂ A)
    (hc : IsLocallyConstant fun v : Fin 2 → G => c (v 0, v 1)) : cocycles A 2 :=
  (cochains A).cyclesMk (mkCochain A _ hc) 3 (by simp) (by
    apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans (inhomogeneousCochains_d_two_eq_zero A c))

theorem cochainOf_cocycleι_cocyclesOfCocycles₂ (c : groupCohomology.cocycles₂ A)
    (hc : IsLocallyConstant fun v : Fin 2 → G => c (v 0, v 1)) :
    cochainOf A (cocycleι A 2 (cocyclesOfCocycles₂ A c hc)) = fun v => c (v 0, v 1) :=
  congrArg (cochainOf A) ((cochains A).i_cyclesMk _ _ _ _)

/-- The comparison with the abstract group carries the class of `cocyclesOfCocycles₂ A c hc` to
Mathlib's class of `c`. -/
theorem toGroupCohomology_cohomologyπ_cocyclesOfCocycles₂ (c : groupCohomology.cocycles₂ A)
    (hc : IsLocallyConstant fun v : Fin 2 → G => c (v 0, v 1)) :
    (toGroupCohomology A 2).hom (cohomologyπ A 2 (cocyclesOfCocycles₂ A c hc)) =
      groupCohomology.H2π A c := by
  rw [toGroupCohomology_cohomologyπ]
  change _ = (groupCohomology.π A 2) ((groupCohomology.isoCocycles₂ A).inv c)
  congr 1
  apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A 2)).1 inferInstance
  rw [iCocycles_cyclesMap_cochainsι, cochainOf_cocycleι_cocyclesOfCocycles₂,
    groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  rfl

end Langlands.ProfiniteCohomology
