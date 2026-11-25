/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Restricting a tensor-Hom transpose with prescribed scalar values

Source: Stacks Project, Modules, Tag 01CN and Tag 01YB, tensor-Hom paragraph.
(blueprint: lem-pc-tensor-hom-restriction-scalar)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules

local instance localInst_TensorHomRestrictionScalar_1
    {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    SMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op W))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (M.val.obj (op W))) :=
  inferInstanceAs (SMul (X.sheaf.obj.obj (op W)) (M.val.obj (op W)))

set_option backward.isDefEq.respectTransparency false in
/-- Transposition sends a local scalar multiple of a Hom section to multiplication
followed by the local morphism. No coherence or ideal-power hypothesis is required.
Source: Stacks Project, Modules, Tag 01CN, and Tag 01YB, tensor-Hom paragraph.
(blueprint: lem-pc-tensor-hom-restriction-scalar)

Proof: For W contained in U, the assumed equality says that alpha_W(a) is
ι_W(a) times the restriction of the local morphism s. Evaluating at g gives
ι_W(a) times s_W(g). The tensor-Hom characterization therefore says beta on
local pure tensors is this same value. Multiplication is the map ι tensor id
followed by the left unitor; its value on a tensor g is ι_W(a) times g.
Linearity of s gives equality of these two local tensor maps. Pure tensors
generate the presheaf tensor product. The universal property of sheafification
then gives equality of the restricted sheaf maps. Finally, naturality of
Scheme.Modules.overFunctorEquiv transports the slice morphism represented by
s to the displayed restrictFunctor morphism. This also applies to the empty
open and zero modules; no generation by global sections of U is assumed. -/
theorem tensorHom_restriction_of_local_scalar
    {X : Scheme.{u}} (A H F : X.Modules)
    (ι : A ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (s : (SheafOfModules.homObj (R := X.sheaf) H F).val.obj (op U))
    (α : A ⟶ SheafOfModules.homObj (R := X.sheaf) H F)
    (hα : ∀ (W : X.Opens) (h : W ≤ U) (a : A.val.obj (op W)),
      α.val.app (op W) a = ι.val.app (op W) a •
        (SheafOfModules.homObj (R := X.sheaf) H F).val.map (homOfLE h).op s) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∀ (β : A ⊗ H ⟶ F),
      (∀ (W : X.Opens) (a : A.val.obj (op W)) (g : H.val.obj (op W)),
        β.val.app (op W)
          ((SheafOfModules.tensorObjIsoSheafification A H).inv.val.app (op W)
            (((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 X.ringCatSheaf.obj)).unit.app (A.val ⊗ H.val)).app (op W)
                (a ⊗ₜ[X.sheaf.obj.obj (op W)] g))) =
          (α.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) →
      (restrictFunctor U.ι).map β =
        (restrictFunctor U.ι).map (ι ▷ H ≫ (λ_ H).hom) ≫
          (overFunctorEquiv U).inv.app H ≫
          (overEquiv U).functor.map (⟨s⟩ : H.over U ⟶ F.over U) ≫
          (overFunctorEquiv U).hom.app F := by
  intro β hβ
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let j := U.ι
  obtain ⟨e, he⟩ := exists_restriction_tensor_comparison j A H
  apply (cancel_epi e.inv).mp
  apply tensor_hom_ext
  intro V a g
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have hev := he V a g
  change e.inv.app V (tmulSection a g) =
    tmulSection (M := A) (N := H) (U := j ''ᵁ V) a g at hev
  rw [hev]
  let W : X.Opens := j ''ᵁ V
  have hW : W ≤ U := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  -- Compute the restriction comparison once, before the sectionwise calculation.
  change β.app W (tmulSection a g) =
    (s.app (op (Over.mk (homOfLE hW)))) ((ι ▷ H ≫ (λ_ H).hom).app W (tmulSection a g))
  have hb := hβ W a g
  change β.app W (tmulSection a g) = _ at hb
  erw [hb]
  rw [hα W hW a]
  change X.sheaf.obj.map (𝟙 (op W)) (show Γ(X, W) from ι.app W a) •
    (s.app (op (Over.mk (homOfLE hW)))) g = _
  rw [X.sheaf.obj.map_id]
  change (show Γ(X, W) from ι.app W a) • (s.app (op (Over.mk (homOfLE hW)))) g = _
  have hm : (ι ▷ H ≫ (λ_ H).hom).app W (tmulSection a g) =
      (show Γ(X, W) from ι.app W a) • (show Γ(H, W) from g) := by
    rw [Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerRight_app_tmulSection]
    exact leftUnitor_hom_app_tmulSection' (M := H) (ι.app W a) g
  rw [hm]
  change (show Γ(X, W) from ι.app W a) • (s.app (op (Over.mk (homOfLE hW)))) g =
    (s.app (op (Over.mk (homOfLE hW))))
      ((show Γ(X, W) from ι.app W a) • (show Γ(H, W) from g))
  exact ((s.app (op (Over.mk (homOfLE hW)))).hom.map_smul _ _).symm

end AlgebraicGeometry.Scheme.Modules
