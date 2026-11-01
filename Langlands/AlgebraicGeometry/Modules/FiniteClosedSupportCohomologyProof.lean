import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyStatement
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.Cohomology.FiniteClosedSupportSheafProof

/-!
# Cohomology and zero detection for scheme modules with finite closed support: proof

Let `M` be an `𝒪_X`-module whose nonzero abelian stalks lie in a finite set of closed points.
The underlying abelian sheaf of `M` satisfies the hypotheses of the published abelian-sheaf
result `Langlands.Cohomology.finiteClosedSupportSheaf`, with `S` the stalk support of `M`. Hence
`M.presheaf` is flasque, and the published flasque-module theorem
`PushforwardInjectiveAcyclic.isZero_cohomology_succ_of_isFlasque` kills every positive-degree
cohomology module. The abelian-sheaf result also detects the zero sheaf by its top sections;
these have the same elements as the global-section module of `M`, and the zero abelian sheaf
has zero stalks, so `M` is zero. The `R`-module versions over an affine base are the
`Γ(X, ⊤)`-module versions with scalars restricted, which keeps the underlying group.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace FiniteClosedSupportCohomology

variable {X : Scheme.{u}} {M : X.Modules}

/-- The underlying abelian sheaf of a module with finite closed support is flasque, and its
top-section group is zero exactly when the abelian sheaf is zero. -/
lemma toSheaf_finiteClosedSupport (h : HasFiniteClosedSupport M) :
    TopCat.Presheaf.IsFlasque M.presheaf ∧
      (IsZero (M.presheaf.obj (op ⊤)) ↔
        IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) :=
  Langlands.Cohomology.finiteClosedSupportSheaf X.toTopCat
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (stalkSupport M) h.1 h.2
    (fun _ hx => not_not.1 hx)

/-- A module with finite closed support has a flasque underlying abelian presheaf. -/
lemma isFlasque (h : HasFiniteClosedSupport M) : TopCat.Presheaf.IsFlasque M.presheaf :=
  (toSheaf_finiteClosedSupport h).1

/-- A module is zero exactly when its underlying abelian sheaf is zero. -/
lemma isZero_iff_isZero_toSheaf :
    IsZero M ↔ IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  isZero_iff_forall_isZero_stalk.trans
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).symm

/-- The global-section module is zero exactly when the top-section abelian group is zero. -/
lemma isZero_globalSections_iff :
    IsZero ((DerivedSections.globalSections X).obj M) ↔ IsZero (M.presheaf.obj (op ⊤)) := by
  rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  rfl

/-- Restriction of scalars of modules preserves and reflects zero objects. -/
lemma isZero_restrictScalars_iff {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (N : ModuleCat.{u} S) : IsZero ((ModuleCat.restrictScalars φ).obj N) ↔ IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- Positive-degree cohomology of a module with finite closed support vanishes. -/
lemma isZero_cohomology_succ (h : HasFiniteClosedSupport M) (n : ℕ) :
    IsZero ((DerivedSections.cohomology X (n + 1)).obj M) := by
  have := isFlasque h
  exact PushforwardInjectiveAcyclic.isZero_cohomology_succ_of_isFlasque n M

/-- Global sections detect the vanishing of a module with finite closed support. -/
lemma isZero_globalSections_iff_isZero (h : HasFiniteClosedSupport M) :
    IsZero ((DerivedSections.globalSections X).obj M) ↔ IsZero M := by
  rw [isZero_globalSections_iff, isZero_iff_isZero_toSheaf]
  exact (toSheaf_finiteClosedSupport h).2

end FiniteClosedSupportCohomology

open FiniteClosedSupportCohomology in
/-- For an actual scheme module with finite closed support, all positive-degree cohomology
vanishes and global sections detect its vanishing, also for the `R`-module versions over
any affine base `Spec R`. -/
theorem finiteClosedSupportCohomology : FiniteClosedSupportCohomologyStatement.{u} := by
  intro X M h
  refine ⟨isZero_cohomology_succ h, isZero_globalSections_iff_isZero h, fun R f => ⟨?_, ?_⟩⟩
  · intro n
    exact ((isZero_restrictScalars_iff _ _).2 (isZero_cohomology_succ h n)).of_iso
      ((DerivedSections.relativeCohomologyRestrictScalarsIso f (n + 1)).app M).symm
  · rw [← ((DerivedSections.relativeGlobalSectionsIso f).app M).isZero_iff,
      Functor.comp_obj, isZero_restrictScalars_iff]
    exact isZero_globalSections_iff_isZero h

end Langlands.AlgebraicGeometry.Modules
