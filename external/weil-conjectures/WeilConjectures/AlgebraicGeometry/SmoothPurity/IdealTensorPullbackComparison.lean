/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealProductImage
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Tensor pullback of an ideal and its extended ideal

Source: Stacks Project, Modules, Tag 01AJ, and Schemes, Tag 01JU.
(blueprint: lem-pur-ideal-tensor-pullback-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem image_comp_right {C : Type*} [Category C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : B ⟶ D) :
    (Subobject.«exists» b).obj (imageSubobject a) = imageSubobject (a ≫ b) := by
  rw [Subobject.exists_obj_eq_imageSubobject]
  conv_rhs =>
    rw [← imageSubobject_arrow_comp a, Category.assoc, imageSubobject_comp_of_epi]

private theorem ideal_product_unit_image {X : Scheme.{u}} {I : X.Modules}
    (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    {M : X.Modules} (e : M ⟶ SheafOfModules.unit X.ringCatSheaf) [IsIso e] :
    imageSubobject (Scheme.idealModuleProductι j M ≫ e) = Subobject.mk j := by
  open MonoidalCategory in
  let μ := j ▷ M ≫ (λ_ M).hom
  have hf : factorThruImage μ ≫ Scheme.idealModuleProductι j M = μ := image.fac μ
  rw [← imageSubobject_comp_of_epi (factorThruImage μ), ← Category.assoc, hf]
  have hm : μ ≫ e = (I ◁ e) ≫ (j ▷ (𝟙_ X.Modules) ≫ (λ_ (𝟙_ X.Modules)).hom) := by
    change (j ▷ M ≫ (λ_ M).hom) ≫ e = _
    calc
      _ = j ▷ M ≫ ((𝟙_ X.Modules) ◁ e ≫ (λ_ (𝟙_ X.Modules)).hom) := by
        rw [leftUnitor_naturality, Category.assoc]
      _ = (I ◁ e ≫ j ▷ (𝟙_ X.Modules)) ≫ (λ_ (𝟙_ X.Modules)).hom := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun a ↦ a ≫ (λ_ (𝟙_ X.Modules)).hom) (whisker_exchange j e).symm)
      _ = _ := Category.assoc _ _ _
  have hu : j ▷ (𝟙_ X.Modules) ≫ (λ_ (𝟙_ X.Modules)).hom = (ρ_ I).hom ≫ j := by
    rw [unitors_equal]
    exact rightUnitor_naturality j
  rw [hm, imageSubobject_iso_comp]
  simp only [hu]
  rw [imageSubobject_iso_comp, imageSubobject_mono]

/-- The canonical tensor-pullback map onto the extended ideal is epi, and is an
isomorphism for flat pullback. Its composite with the ideal inclusion fixes it uniquely.
Source: Stacks Project, Modules, Tag 01AJ, and Schemes, Tag 01JU.
(blueprint: lem-pur-ideal-tensor-pullback-comparison).

Proof: Tensor the ideal inclusion and compose with the structure-module comparison.
The pullback ideal-product image theorem, applied to the unit module, identifies its
image with the extended ideal. Factor through this image. The factor is epi and its
composite with the monic ideal inclusion determines it uniquely. Under flat pullback
the original inclusion remains monic, so the factor is both mono and epi and hence
an isomorphism in the abelian category of module sheaves. -/
theorem existsUnique_idealTensorPullbackComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (J : Y.IdealSheafData) :
    ∃! d : (Scheme.Modules.tensorPullback g).obj J.toModules ⟶ (J.comap g).toModules,
      d ≫ (J.comap g).toModulesι =
        (Scheme.Modules.tensorPullback g).map J.toModulesι ≫
          Scheme.Modules.tensorPullbackObjUnitToUnit g ∧
      Epi d ∧ (Flat g → IsIso d) := by
  classical
  open MonoidalCategory in
  let T := Scheme.Modules.tensorPullback g
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let := adj.isLeftAdjoint
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let j := J.toModulesι
  let ε := Scheme.Modules.tensorPullbackObjUnitToUnit g
  have : IsIso ε := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g).1
  let μ := j ▷ O ≫ (λ_ O).hom
  have hμ : μ = (ρ_ J.toModules).hom ≫ j := by
    change j ▷ (𝟙_ Y.Modules) ≫ (λ_ (𝟙_ Y.Modules)).hom = _
    rw [unitors_equal]
    exact rightUnitor_naturality j
  have hs : imageSubobject (T.map j ≫ ε) =
      imageSubobject (T.map (Scheme.idealModuleProductι j O) ≫ ε) := by
    calc
      _ = imageSubobject (T.map μ ≫ ε) := by
        simp only [hμ, T.map_comp, Category.assoc, imageSubobject_iso_comp]
      _ = _ := by
        conv_lhs => rw [← image.fac μ]
        simp only [T.map_comp, Category.assoc, imageSubobject_comp_of_epi]
        rfl
  have hp := modulePullbackIdealProductImage g J O
    (SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf))
  have ht := congrArg (fun K ↦ (Subobject.«exists» ε).obj K) hp
  rw [image_comp_right, image_comp_right] at ht
  have he : imageSubobject (T.map j ≫ ε) = Subobject.mk (J.comap g).toModulesι := by
    rw [hs, ht]
    exact ideal_product_unit_image (J.comap g).toModulesι ε
  let e := Subobject.isoOfMkEqMk (image.ι (T.map j ≫ ε)) (J.comap g).toModulesι he
  let d := factorThruImage (T.map j ≫ ε) ≫ e.hom
  have hd : d ≫ (J.comap g).toModulesι = T.map j ≫ ε := by
    dsimp only [d]
    simp [e]
  have hd_epi : Epi d := by dsimp [d]; infer_instance
  refine ⟨d, ⟨hd, hd_epi, ?_⟩, ?_⟩
  · intro hg
    have : Flat g := hg
    have : PreservesFiniteLimits T := (flat_module_pullback_exact_pushforward_injective g).1.1
    have : Mono (T.map j ≫ ε) := inferInstance
    have : Mono (d ≫ (J.comap g).toModulesι) := by rw [hd]; infer_instance
    have : Mono d := mono_of_mono d (J.comap g).toModulesι
    exact isIso_of_mono_of_epi d
  · intro d' hd'
    exact (cancel_mono (J.comap g).toModulesι).1 (hd'.1.trans hd.symm)

end AlgebraicGeometry
