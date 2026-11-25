/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealProductImage
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# The ideal sheaf of a base-changed closed subscheme

Source: Stacks Project, Schemes, Lemma 26.17.6, Tag 01JU (1)
(blueprint: lem-pc-closed-subscheme-base-change-ideal-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

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

/-- The projection of the base change of a closed immersion is a closed immersion,
and its kernel ideal is the image of the pulled-back ideal inclusion followed by the
adjoint of the structure-sheaf map. The adjunction is the one supplied by the tensor
pullback dependency; its choice does not affect the image subobject.
Source: Stacks Project, Schemes, Tag 01JU (1)
(blueprint: lem-pc-closed-subscheme-base-change-ideal-image).
Proof: apply `lem-pc-closed-imm-base-change` to `i : Z ⟶ S` and `g : Y ⟶ S`.
Its projection and ideal-image assertions are precisely these two conclusions.
Equivalently, Tag 01JU constructs the closed subscheme defined by this image ideal,
identifies it with the fibre product of locally ringed spaces, and observes it is a scheme. -/
theorem closedSubscheme_baseChange_ideal_image {S Z Y : Scheme.{u}}
    (i : Z ⟶ S) [IsClosedImmersion i] (g : Y ⟶ S) :
    IsClosedImmersion (pullback.snd i g) ∧
      Subobject.mk (pullback.snd i g).ker.toModulesι =
        imageSubobject
          ((Scheme.Modules.tensorPullback g).map i.ker.toModulesι ≫
            ((Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction g)).homEquiv
              (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf)).symm
                (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) := by
  open MonoidalCategory in
  classical
  refine ⟨inferInstance, ?_⟩
  let T := Scheme.Modules.tensorPullback g
  let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction g)
  let a₀ := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let c := adj.leftAdjointUniq a₀
  let ε := (adj.homEquiv (SheafOfModules.unit S.ringCatSheaf)
    (SheafOfModules.unit Y.ringCatSheaf)).symm
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  have hε : ε = (c.app (SheafOfModules.unit S.ringCatSheaf)).hom ≫
      Scheme.Modules.tensorPullbackObjUnitToUnit g := by
    dsimp [ε, Scheme.Modules.tensorPullbackObjUnitToUnit]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [← c.hom.naturality_assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit g) :=
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g).1
  have : IsIso ε := by rw [hε]; infer_instance
  let := adj.isLeftAdjoint
  let O : S.Modules := SheafOfModules.unit S.ringCatSheaf
  let j := i.ker.toModulesι
  let μ := j ▷ O ≫ (λ_ O).hom
  have hμ : μ = (ρ_ i.ker.toModules).hom ≫ j := by
    change j ▷ (𝟙_ S.Modules) ≫ (λ_ (𝟙_ S.Modules)).hom = _
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
  have hp := modulePullbackIdealProductImage g i.ker O
    (SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf))
  have ht := congrArg (fun K ↦ (Subobject.«exists» ε).obj K) hp
  rw [image_comp_right, image_comp_right] at ht
  have hker : (pullback.snd i g).ker = i.ker.comap g := by
    calc
      _ = (pullback.fst g i).ker := by
        rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry i g).hom
          (pullback.fst g i), pullbackSymmetry_hom_comp_fst]
      _ = _ := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i g
  change Subobject.mk (pullback.snd i g).ker.toModulesι = imageSubobject (T.map j ≫ ε)
  rw [hker, hs, ht]
  exact (ideal_product_unit_image (i.ker.comap g).toModulesι ε).symm

end
end AlgebraicGeometry
