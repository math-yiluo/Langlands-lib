/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCupNaiveMap
import WeilConjectures.Algebra.Category.ModuleCat.CocontinuousGenerator
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
/-! # Tensor-counit normalization of the global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
local instance globalPullbackMatesCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalPullbackMatesMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalPullbackMatesSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
local instance globalPullbackMatesColimits :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance globalPullbackMatesPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalPullbackMatesClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
private def sectionsTopEquiv (M : X.Modules) : M.sections ≃ Γ(M, ⊤) where
  toFun s := s.val (op ⊤)
  invFun x := PresheafOfModules.sectionsMk
    (fun U ↦ M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op x)
    (fun U V f ↦ by
      rw [← PresheafOfModules.map_comp_apply]
      rfl)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE (le_top : U.unop ≤ ⊤)).op
  right_inv x := by
    change M.val.map (𝟙 (op ⊤)) x = x
    simp

private def unitHomTopEquiv (M : X.Modules) : (𝟙_ X.Modules ⟶ M) ≃ Γ(M, ⊤) :=
  (SheafOfModules.unitHomEquiv M).trans (sectionsTopEquiv X M)

private theorem unitMate_isIso
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace) :
    IsIso ((adj.homEquiv (𝟙_ _) (𝟙_ _)).symm
      (ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap)) := by
  let ε : (𝟙_ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
    ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  let e : ((𝟙_ (ModuleCat.{u} (Γ(X, ⊤)))) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M) ≃ Γ(M, ⊤) :=
    ModuleCat.homEquiv.trans
      (LinearMap.ringLmapEquivSelf Γ(X, ⊤) ℤ Γ(M, ⊤)).toEquiv
  have he : Function.Bijective (fun f : 𝟙_ X.Modules ⟶ M ↦
      ε ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f) := by
    have h : (fun f : 𝟙_ X.Modules ⟶ M ↦
        ε ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f) =
        e.symm ∘ unitHomTopEquiv X M := by
      funext f
      apply e.injective
      change f.val.app (op ⊤) (unitSectionsEquiv (X := X) ⊤ 1) = _
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      rfl
    rw [h]
    exact e.symm.bijective.comp (unitHomTopEquiv X M).bijective
  have h : (fun f : 𝟙_ X.Modules ⟶ M ↦
      (adj.homEquiv (𝟙_ _) (𝟙_ _)).symm ε ≫ f) =
      (adj.homEquiv _ M).symm ∘
        (fun f : 𝟙_ X.Modules ⟶ M ↦
          ε ≫ (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f) := by
    funext f
    exact (adj.homEquiv_naturality_right_symm ε f).symm
  change Function.Bijective (fun f : 𝟙_ X.Modules ⟶ M ↦
    (adj.homEquiv (𝟙_ _) (𝟙_ _)).symm ε ≫ f)
  rw [h]
  exact (adj.homEquiv _ M).symm.bijective.comp he

/-- The unit and tensor mates for global sections are isomorphisms.
Source: Stacks, Modules Lemma 17.16.4 (Tag 01CA), and Sheaves Tags 008A and 008Y.
(blueprint: lem-sc-global-tensor-pullback-mates-isiso)
Proof: let A be the global section ring and p the ringed-space map from X to the
one-point ringed space with ring A. Point evaluation identifies its module category
with A-modules, and the inverse-image/change-of-rings adjunction identifies the left
adjoint of global sections with p*. For this adjunction the unit mate is the canonical
map p*(A) to O_X, with local formula a tensor r maps to ar, and inverse r maps to
r tensor 1. The tensor mate sends a tensor (m tensor n) to
(a tensor m) tensor (1 tensor n). Its inverse sends
(a tensor m) tensor (b tensor n) to ab tensor (m tensor n). The tensor balancing
relations make these maps well defined and mutually inverse. Inverse image and
sheafification preserve these local formulas, giving the sheaf isomorphisms of
Lemma 17.16.4. The Hom equivalence identifies these maps with exactly the two mates
in the statement: the tensor mate is transposed from the tensor of the two adjunction
units followed by the section tensor map. For any other left adjoint P and adjunction,
the unique isomorphism of left adjoints compatible with the units conjugates these
mates by isomorphisms, so they remain isomorphisms. No flatness, finite generation,
or nonempty-space hypothesis is used; zero modules and the empty scheme obey the
same formulas. -/
theorem globalTensorPullback_mates_isIso
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace) :
    IsIso ((adj.homEquiv (𝟙_ _) (𝟙_ _)).symm
      (ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap)) ∧
    ∀ A B : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)),
      IsIso ((adj.homEquiv _ _).symm
        ((adj.unit.app A ⊗ₘ adj.unit.app B) ≫
          moduleCup_sectionTensorMap X (P.obj A) (P.obj B))) := by
  have hunit := unitMate_isIso X P adj
  refine ⟨hunit, ?_⟩
  have : P.IsLeftAdjoint := adj.isLeftAdjoint
  intro A B
  let α : tensorRight B ⋙ P ⟶ P ⋙ tensorRight (P.obj B) :=
    { app := fun C ↦ (adj.homEquiv _ _).symm
        ((adj.unit.app C ⊗ₘ adj.unit.app B) ≫
          moduleCup_sectionTensorMap X (P.obj C) (P.obj B))
      naturality := by
        intro C D f
        dsimp
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simp only [Equiv.apply_symm_apply]
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro c b
        change tmulSection ((adj.unit.app D).hom (f.hom c))
            ((adj.unit.app B).hom b) =
          (P.map f ▷ P.obj B).val.app (op ⊤)
            (tmulSection ((adj.unit.app C).hom c) ((adj.unit.app B).hom b))
        calc
          _ = tmulSection
              ((P.map f).val.app (op ⊤) ((adj.unit.app C).hom c))
              ((adj.unit.app B).hom b) := by
            congr 1
            exact congrArg (fun g ↦ g.hom c) (adj.unit.naturality f)
          _ = _ := (whiskerRight_app_tmulSection (X := X) (P.map f)
            ((adj.unit.app C).hom c) ((adj.unit.app B).hom b)).symm }
  let ε : (𝟙_ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))) ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
    ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap
  let η := (adj.homEquiv (𝟙_ _) (𝟙_ _)).symm ε
  have hη : IsIso η := hunit
  have hbase : IsIso (α.app (ModuleCat.of (Γ(X, ⊤)) (Γ(X, ⊤)))) := by
    have hfac : α.app (𝟙_ _) ≫ (η ▷ P.obj B) ≫ (λ_ (P.obj B)).hom =
        P.map (λ_ B).hom := by
      apply (adj.homEquiv _ _).injective
      have hmap : adj.homEquiv _ _ (P.map (λ_ B).hom) =
          (λ_ B).hom ≫ adj.unit.app B := by
        rw [Adjunction.homEquiv_unit]
        exact (adj.unit.naturality (λ_ B).hom).symm
      rw [adj.homEquiv_naturality_right]
      refine Eq.trans ?_ hmap.symm
      simp only [α, Equiv.apply_symm_apply]
      change ((adj.unit.app (𝟙_ _) ⊗ₘ adj.unit.app B) ≫
        moduleCup_sectionTensorMap X _ _) ≫ _ = (λ_ B).hom ≫ adj.unit.app B
      have hηunit := (adj.homEquiv (𝟙_ _) (𝟙_ _)).apply_symm_apply ε
      rw [Adjunction.homEquiv_unit] at hηunit
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro r b
      change Γ(X, ⊤) at r
      change (λ_ (P.obj B)).hom.val.app (op ⊤)
        ((η ▷ P.obj B).val.app (op ⊤)
          (tmulSection ((adj.unit.app (𝟙_ _)).hom r) ((adj.unit.app B).hom b))) =
        (adj.unit.app B).hom (r • b)
      have hr := congrArg (fun g ↦ g.hom r) hηunit
      change η.val.app (op ⊤) ((adj.unit.app (𝟙_ _)).hom r) =
        unitSectionsEquiv (X := X) ⊤ r at hr
      calc
        _ = (λ_ (P.obj B)).hom.val.app (op ⊤)
            (tmulSection (unitSectionsEquiv (X := X) ⊤ r) ((adj.unit.app B).hom b)) := by
          congr 1
          exact (whiskerRight_app_tmulSection (X := X) η
            ((adj.unit.app (𝟙_ _)).hom r) ((adj.unit.app B).hom b)).trans
              (congrArg (fun s ↦ tmulSection s ((adj.unit.app B).hom b)) hr)
        _ = r • (adj.unit.app B).hom b :=
          leftUnitor_hom_app_tmulSection (X := X) r ((adj.unit.app B).hom b)
        _ = _ := ((adj.unit.app B).hom.map_smul r b).symm
    exact IsIso.of_isIso_fac_right hfac
  exact ModuleCat.isIso_app_of_rankOne α hbase A

end
end AlgebraicGeometry.Scheme.Modules
