import Langlands.AlgebraicGeometry.Modules.IdealAdicMultipleSections
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

/-! # Ideal multiples with the Čech module scalar action -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (M : X.Modules)

/-- The sectionwise base scalar agrees with the scalar used in the Čech model. -/
lemma scalar_eq_algebraMap (U : X.Opens) (r : R) :
    scalar f U r = (Scheme.TwoAffineOpenCover.algebraOfHom f U).algebraMap r := by
  rfl

/-- The ideal-multiple scalar action agrees with the module action in `ofModules`. -/
lemma scalar_smul_eq_ofModules (U : X.Opens) (r : R) (x : Γ(M, U)) :
    scalar f U r • x =
      r • (show (OModulePresheaf.ofModules f M).obj U from x) := by
  rw [OModulePresheaf.ofModules_algebraMap_smul, ← scalar_eq_algebraMap]

/-- The actual inclusion on sections, with the base-ring linear structure of the Čech model. -/
def inclusionSections (U : X.Opens) :
    (OModulePresheaf.ofModules f (multiple f J M)).obj U →ₗ[R]
      (OModulePresheaf.ofModules f M).obj U where
  toFun := (inclusion f J M).app U
  map_add' := map_add _
  map_smul' r x := by
    rw [← scalar_smul_eq_ofModules, ← scalar_smul_eq_ofModules]
    exact (inclusion f J M).app_smul (U := U) (scalar f U r) x

/-- The sectionwise span of local products equals the ideal multiple for the Čech base action. -/
lemma mem_multiplePresubmodule_iff_smul_top (U : X.Opens) (x : Γ(M, U)) :
    x ∈ (multiplePresubmodule f J M).obj (op U) ↔
      (show (OModulePresheaf.ofModules f M).obj U from x) ∈
        J • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).obj U)) := by
  let : CommRing (X.ringCatSheaf.obj.obj (op U)) :=
    inferInstanceAs (CommRing Γ(X, U))
  let : Module R Γ(M, U) := (OModulePresheaf.ofModules f M).module U
  let : Module (X.ringCatSheaf.obj.obj (op U)) Γ(M, U) :=
    inferInstanceAs (Module Γ(X, U) Γ(M, U))
  let : SMulCommClass (X.ringCatSheaf.obj.obj (op U)) Γ(X, U) Γ(M, U) :=
    inferInstanceAs (SMulCommClass Γ(X, U) Γ(X, U) Γ(M, U))
  let P := J • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).obj U))
  constructor
  · intro hx
    change x ∈ Submodule.span _ _ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, m, rfl⟩ := hy
      rw [scalar_smul_eq_ofModules]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    | zero => exact P.zero_mem
    | add y z hy hz h₁ h₂ => exact P.add_mem h₁ h₂
    | smul a y hy h =>
      refine Submodule.smul_induction_on (p := fun z => a • z ∈ P) h ?_ ?_
      · intro r hr m hm
        rw [← scalar_smul_eq_ofModules, smul_comm a (scalar f U r),
          scalar_smul_eq_ofModules]
        exact Submodule.smul_mem_smul hr (Submodule.mem_top)
      · intro y z hy hz
        simpa only [smul_add] using P.add_mem hy hz
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      rw [← scalar_smul_eq_ofModules]
      exact Submodule.subset_span ⟨r, hr, m, rfl⟩
    · intro y z hy hz
      exact ((multiplePresubmodule f J M).obj (op U)).add_mem hy hz

/-- On an affine open the actual inclusion has exactly the ideal-multiple range in the Čech model. -/
lemma range_inclusionSections [M.IsQuasicoherent] (hJ : J.FG)
    {U : X.Opens} (hU : IsAffineOpen U) :
    LinearMap.range (inclusionSections f J M U) =
      J • (⊤ : Submodule R ((OModulePresheaf.ofModules f M).obj U)) := by
  ext x
  exact (mem_range_inclusion_app_iff f J M hJ hU x).trans
    (mem_multiplePresubmodule_iff_smul_top f J M U x)

end Langlands.AlgebraicGeometry.Modules.IdealAdic
