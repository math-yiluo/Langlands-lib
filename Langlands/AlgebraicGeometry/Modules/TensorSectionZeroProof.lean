import Langlands.AlgebraicGeometry.Modules.TensorSectionZeroStatement
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Zero tests for tensor products of actual sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

open Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) : (Scheme.Modules.toPresheafOfModules X).Additive :=
  inferInstanceAs (SheafOfModules.forget X.ringCatSheaf).Additive

local instance (X : Scheme.{u}) : (sheafify X).Additive :=
  (sheafifyAdjunction X).left_adjoint_additive

open MonoidalCategory in
private lemma tensorMap_zero_left {M M' N N' : X.Modules} (g : N ⟶ N') :
    tensorMap (0 : M ⟶ M') g = 0 := by
  have hz : (0 : M ⟶ M').val ⊗ₘ g.val = 0 := by
    apply PresheafOfModules.hom_ext
    intro U
    change (0 : M.val.obj U ⟶ M'.val.obj U) ⊗ₘ g.val.app U = 0
    exact MonoidalPreadditive.zero_tensor _
  change (sheafify X).map ((0 : M ⟶ M').val ⊗ₘ g.val) = 0
  rw [hz, Functor.map_zero]

open MonoidalCategory in
private lemma tensorMap_zero_right {M M' N N' : X.Modules} (f : M ⟶ M') :
    tensorMap f (0 : N ⟶ N') = 0 := by
  have hz : f.val ⊗ₘ (0 : N ⟶ N').val = 0 := by
    apply PresheafOfModules.hom_ext
    intro U
    change f.val.app U ⊗ₘ (0 : N.val.obj U ⟶ N'.val.obj U) = 0
    exact MonoidalPreadditive.tensor_zero _
  change (sheafify X).map (f.val ⊗ₘ (0 : N ⟶ N').val) = 0
  rw [hz, Functor.map_zero]

/-- A zero first section gives a zero tensor section. -/
lemma tensorSection_zero_left (M N : X.Modules) (t : GlobalSections N) :
    tensorSection M N 0 t = 0 := by
  rw [← sectionHom_eq_zero_iff, sectionHom_tensorSection,
    (sectionHom_eq_zero_iff M 0).mpr rfl, tensorMap_zero_left, comp_zero]

/-- A zero second section gives a zero tensor section. -/
lemma tensorSection_zero_right (M N : X.Modules) (s : GlobalSections M) :
    tensorSection M N s 0 = 0 := by
  rw [← sectionHom_eq_zero_iff, sectionHom_tensorSection,
    (sectionHom_eq_zero_iff N 0).mpr rfl, tensorMap_zero_right, comp_zero]

/-- Tensoring with a global frame on the right preserves and reflects zero. -/
lemma tensorSection_eq_zero_iff_of_isIso_right (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (sectionHom N t)] :
    tensorSection M N s t = 0 ↔ s = 0 := by
  have hsplit : tensorMap (sectionHom M s) (sectionHom N t) =
      tensorMap (sectionHom M s) (𝟙 (structureSheaf X)) ≫
        tensorMap (𝟙 M) (sectionHom N t) := by
    rw [tensorMap_comp, Category.comp_id, Category.id_comp]
  have : IsIso (tensorMap (𝟙 M) (sectionHom N t)) :=
    inferInstanceAs (IsIso ((tensorFunctor X).mapIso
      ((Iso.refl M).prod (asIso (sectionHom N t)))).hom)
  rw [← sectionHom_eq_zero_iff, sectionHom_tensorSection,
    comp_eq_zero_iff_of_epi, hsplit, comp_eq_zero_iff_of_mono,
    ← comp_eq_zero_iff_of_mono (tensorRightUnitor M).hom,
    tensorRightUnitor_naturality, comp_eq_zero_iff_of_epi, sectionHom_eq_zero_iff]

/-- Tensoring with a global frame on the left preserves and reflects zero. -/
lemma tensorSection_eq_zero_iff_of_isIso_left (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (sectionHom M s)] :
    tensorSection M N s t = 0 ↔ t = 0 := by
  have hsplit : tensorMap (sectionHom M s) (sectionHom N t) =
      tensorMap (𝟙 (structureSheaf X)) (sectionHom N t) ≫
        tensorMap (sectionHom M s) (𝟙 N) := by
    rw [tensorMap_comp, Category.id_comp, Category.comp_id]
  have : IsIso (tensorMap (sectionHom M s) (𝟙 N)) :=
    inferInstanceAs (IsIso ((tensorFunctor X).mapIso
      ((asIso (sectionHom M s)).prod (Iso.refl N))).hom)
  rw [← sectionHom_eq_zero_iff, sectionHom_tensorSection,
    comp_eq_zero_iff_of_epi, hsplit, comp_eq_zero_iff_of_mono,
    ← comp_eq_zero_iff_of_mono (tensorLeftUnitor N).hom,
    tensorLeftUnitor_naturality, comp_eq_zero_iff_of_epi, sectionHom_eq_zero_iff]

/-- Pullback of a tensor section and the tensor of pulled-back sections have the same zero test. -/
lemma pullback_tensorSection_eq_zero_iff (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) :
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      tensorSection ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
        (pullbackSection f M s) (pullbackSection f N t) = 0 := by
  let P := Scheme.Modules.pullback f
  let c := pullbackTensorComparison f
  have : IsIso c := pullbackTensorComparisonIsIso f
  let ι := pullbackUnitIso f
  let fs := sectionHom M s
  let ft := sectionHom N t
  have hnat : P.map (tensorMap fs ft) ≫ c.app (M, N) =
      c.app (structureSheaf X, structureSheaf X) ≫ tensorMap (P.map fs) (P.map ft) :=
    c.naturality (X := (structureSheaf X, structureSheaf X)) (Y := (M, N)) (fs, ft)
  have hcomp : P.map (tensorMap fs ft) = 0 ↔ tensorMap (P.map fs) (P.map ft) = 0 := by
    rw [← comp_eq_zero_iff_of_mono (c.app (M, N)), hnat, comp_eq_zero_iff_of_epi]
  have hunit : tensorMap (ι.inv ≫ P.map fs) (ι.inv ≫ P.map ft) =
      tensorMap ι.inv ι.inv ≫ tensorMap (P.map fs) (P.map ft) :=
    (tensorMap_comp _ _ _ _).symm
  have : IsIso (tensorMap ι.inv ι.inv) :=
    inferInstanceAs (IsIso ((tensorFunctor Y).mapIso (ι.symm.prod ι.symm)).hom)
  rw [pullbackSection_eq_zero_iff, sectionHom_tensorSection, Functor.map_comp,
    comp_eq_zero_iff_of_epi, hcomp, ← sectionHom_eq_zero_iff,
    sectionHom_tensorSection, comp_eq_zero_iff_of_epi,
    sectionHom_pullbackSection, sectionHom_pullbackSection]
  change tensorMap (P.map fs) (P.map ft) = 0 ↔
    tensorMap (ι.inv ≫ P.map fs) (ι.inv ≫ P.map ft) = 0
  rw [hunit, comp_eq_zero_iff_of_epi]

/-- A right-hand section that becomes a frame after pullback can be cancelled in a zero test. -/
lemma pullback_tensorSection_eq_zero_iff_of_isIso_right (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (pullbackSectionHom f N t)] :
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      pullbackSection f M s = 0 := by
  have : IsIso (sectionHom ((Scheme.Modules.pullback f).obj N) (pullbackSection f N t)) := by
    rw [sectionHom_pullbackSection]
    infer_instance
  rw [pullback_tensorSection_eq_zero_iff, tensorSection_eq_zero_iff_of_isIso_right]

/-- The corresponding zero test with a frame in the left-hand factor after pullback. -/
lemma pullback_tensorSection_eq_zero_iff_of_isIso_left (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) [IsIso (pullbackSectionHom f M s)] :
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      pullbackSection f N t = 0 := by
  have : IsIso (sectionHom ((Scheme.Modules.pullback f).obj M) (pullbackSection f M s)) := by
    rw [sectionHom_pullbackSection]
    infer_instance
  rw [pullback_tensorSection_eq_zero_iff, tensorSection_eq_zero_iff_of_isIso_left]

/-- All five tensor-section zero assertions in arbitrary universe. -/
theorem tensorSectionZero : TensorSectionZeroStatement.{u} :=
  ⟨fun _ M N t ↦ tensorSection_zero_left M N t,
    fun _ M N s ↦ tensorSection_zero_right M N s,
    fun _ M N s t _ ↦ tensorSection_eq_zero_iff_of_isIso_right M N s t,
    fun _ M N s t _ ↦ tensorSection_eq_zero_iff_of_isIso_left M N s t,
    fun _ _ f M N s t ↦ pullback_tensorSection_eq_zero_iff f M N s t⟩

end Langlands.SchemeModule
