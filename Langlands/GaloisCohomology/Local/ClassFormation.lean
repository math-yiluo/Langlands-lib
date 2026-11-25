import Langlands.Cohomology.Profinite.ClassFormation.HighDegree
import Langlands.GaloisCohomology.Local.Invariant

/-!
# The class formation of a local field

For a nonarchimedean local field `K` with separable closure `Ksep`, the units `Ksepˣ` form a class
formation for `Gal(Ksep/K)`: on every open subgroup `U` the invariant
`H²(U, Ksepˣ) ≃ ℚ/ℤ` is `openInvariant K U` (the Library's local invariant of the fixed field of
`U`), `H¹(U, Ksepˣ) = 0` is Hilbert 90, and restriction multiplies the invariant by the relative
index. On `U = Gal(Ksep/K)` the invariant is `invariant K Ksep`. Consequences: the cohomology of
`Ksepˣ` vanishes in degrees `≥ 3`.
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open CategoryTheory IntermediateField Langlands.ProfiniteCohomology ClassFieldTheory.Local

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The class formation `(Gal(Ksep/K), Ksepˣ)` of a nonarchimedean local field. -/
def classFormation : ClassFormation (unitsModule K Ksep) :=
  ClassFormation.ofAddEquiv (openInvariant K) isZero_cohomology_one_res_unitsModule
    (openInvariant_resOfLE K)

@[simp]
theorem classFormation_invEquiv (U : OpenSubgroup Gal(Ksep/K)) :
    (classFormation K Ksep).invEquiv U = openInvariant K U :=
  ClassFormation.invEquiv_ofAddEquiv _ _ _ U

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Restriction to the open subgroup `⊤` is restriction to its fixed field. -/
theorem res_top_comp_openCohomologyIso (n : ℕ) :
    res (unitsModule K Ksep) ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) n ≫
        (openCohomologyIso (⊤ : OpenSubgroup Gal(Ksep/K)) n).hom =
      unitsRestriction K (fixedField ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)))
        Ksep n := by
  rw [openCohomologyIso_hom, res, unitsRestriction]
  refine (map_comp _ _ _ _ n).symm.trans ?_
  apply ProfiniteCohomology.map_congr
  · exact ContinuousMonoidHom.ext fun σ => AlgEquiv.ext fun x =>
      (krullRestriction_self_apply _ _ Ksep σ x).symm
  · intro a
    exact Units.ext rfl

/-- The invariant of the class formation on `Gal(Ksep/K)` itself is `invariant K Ksep`. -/
theorem openInvariant_res_top (x : cohomology (unitsModule K Ksep) 2) :
    openInvariant K (⊤ : OpenSubgroup Gal(Ksep/K))
        ((res (unitsModule K Ksep) ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) 2).hom
          x) = invariant K Ksep x := by
  set E := fixedField ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))
  have hsq := congrArg (fun φ => φ.hom x) (res_top_comp_openCohomologyIso K Ksep 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  let := LocalField.FiniteExtension.normedField K E
  let := LocalField.FiniteExtension.valuativeRel K E
  let := LocalField.FiniteExtension.isLocalField K E
  have : ValuativeExtension K E := spectralFiniteExtension_valuativeExtension K E
  have hdeg : Module.finrank K E = 1 := by
    rw [← index_openSubgroup]
    exact Subgroup.index_top
  rw [openInvariant_apply, hsq,
    invariant_unitsRestriction K Ksep E (spectralFiniteExtension_algebraMap_continuous K E), hdeg,
    one_nsmul]

theorem classFormation_invEquiv_res_top (x : cohomology (unitsModule K Ksep) 2) :
    (classFormation K Ksep).invEquiv ⊤
        ((res (unitsModule K Ksep) ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) 2).hom
          x) = invariant K Ksep x := by
  rw [classFormation_invEquiv, openInvariant_res_top]

/-- `Hʳ(U, Ksepˣ) = 0` for every open subgroup `U` of `Gal(Ksep/K)` and `r ≥ 3`. -/
theorem subsingleton_cohomology_res_unitsModule_of_three_le (U : OpenSubgroup Gal(Ksep/K)) {r : ℕ}
    (hr : 3 ≤ r) :
    Subsingleton (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) r) :=
  (classFormation K Ksep).subsingleton_cohomology_of_three_le U hr

/-- `Hʳ(Gal(Ksep/K), Ksepˣ) = 0` for `r ≥ 3`. -/
theorem subsingleton_cohomology_unitsModule_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology (unitsModule K Ksep) r) :=
  (classFormation K Ksep).subsingleton_cohomology_top_of_three_le hr

end Langlands.GaloisCohomology.Local
