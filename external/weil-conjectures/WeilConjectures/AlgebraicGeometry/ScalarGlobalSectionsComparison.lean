/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Canonical degree-zero and external global-section maps

Source: Stacks Project, Tags 01DZ, 0BED.
(blueprint: def-sc-scalar-global-sections-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Degree-zero derived sections are ordinary sections, with scalars restricted along f.
Source: Stacks Project, Tag 01DZ. -/
def scalarGlobalSectionsEquiv (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    scalarCohomology f F 0 ≃ₗ[k] scalarObj f F (op ⊤) := by
  letI : EnoughInjectives (SheafOfModules.{w} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))
  let e := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf.app F
  exact ((ModuleCat.restrictScalars (scalarMap f ⊤)).mapIso e).toLinearEquiv

/-- The tensor-pullback adjunction unit on global sections, restricted to the top open.
Source: Stacks Project, Tags 0096, 0BED. -/
def tensorPullbackTopSection (a : Y ⟶ X) (F : X.Modules) (s : F.val.obj (op ⊤)) :
    ((tensorPullback a).obj F).val.obj (op ⊤) :=
  ((tensorPullback a).obj F).val.map (homOfLE (by simp : ⊤ ≤ a ⁻¹ᵁ ⊤)).op
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).val.app (op ⊤) s)

private theorem tensorPullbackTopSection_add (a : Y ⟶ X) (F : X.Modules)
    (s t : F.val.obj (op ⊤)) :
    tensorPullbackTopSection a F (s + t) =
      tensorPullbackTopSection a F s + tensorPullbackTopSection a F t := by
  simp only [tensorPullbackTopSection, map_add]

private theorem tensorPullbackTopSection_smul
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules)
    (r : k) (s : scalarObj f F (op ⊤)) :
    tensorPullbackTopSection a F (r • s) =
      (scalarMap g ⊤ r) • tensorPullbackTopSection a F s := by
  change tensorPullbackTopSection a F ((scalarMap f ⊤ r) • (show F.val.obj (op ⊤) from s)) = _
  unfold tensorPullbackTopSection
  change ((tensorPullback a).obj F).presheaf.map _
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).app ⊤
      ((scalarMap f ⊤ r) • (show F.val.obj (op ⊤) from s))) = _
  rw [Hom.app_smul]
  change ((tensorPullback a).obj F).presheaf.map
    (homOfLE (by simp : ⊤ ≤ a ⁻¹ᵁ ⊤)).op
    ((a.app ⊤).hom (scalarMap f ⊤ r) •
      (show Γ((tensorPullback a).obj F, a ⁻¹ᵁ ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).app ⊤ s)) = _
  rw [Scheme.Modules.map_smul]
  congr 1
  subst g
  simp only [scalarMap, RingHom.comp_apply]
  simp [Scheme.Hom.appTop]

/-- The bilinear external product of global sections, using tensor-pullback units.
Source: Stacks Project, Varieties, Tag 0BED, maps preceding equation-kunneth-on-cech. -/
def externalGlobalSectionsBilinear
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    scalarObj f F (op ⊤) →ₗ[k] scalarObj g G (op ⊤) →ₗ[k]
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (op ⊤) := by
  exact LinearMap.mk₂ k
    (fun s t ↦ tmulSection
      (tensorPullbackTopSection (pullback.fst f g) F s)
      (tensorPullbackTopSection (pullback.snd f g) G t))
    (by intros; rw [tensorPullbackTopSection_add, add_tmulSection])
    (by
      intro r s t
      rw [tensorPullbackTopSection_smul f (pullback.fst f g ≫ f)
        (pullback.fst f g) rfl, smul_tmulSection]
      rfl)
    (by intros; rw [tensorPullbackTopSection_add, tmulSection_add])
    (by
      intro r s t
      rw [tensorPullbackTopSection_smul g (pullback.fst f g ≫ f)
        (pullback.snd f g) pullback.condition.symm, tmulSection_smul]
      rfl)

/-- The canonical linear map induced by the external product of sections.
Source: Stacks Project, Varieties, Tag 0BED.
(blueprint: def-sc-scalar-global-sections-comparison). -/
def externalGlobalSectionsTensor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    (scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op ⊤)) →ₗ[k]
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (op ⊤) :=
  TensorProduct.lift (externalGlobalSectionsBilinear f g F G)

end
end AlgebraicGeometry.Scheme.Modules
