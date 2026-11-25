/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.BalancedTensorContraction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.BalancedTensorOriginalSectionsExt
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Invertibility of the balanced sheaf tensor map

Source: Stacks Project, Cohomology, Tag 08DE, proof.
(blueprint: lem-pc-balanced-sheaf-tensor-comparison-isIso)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

variable {Z : TopCat.{u}} {R B : Z.Sheaf CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).map a

private theorem tensor_sections_hom_ext
    (S : Z.Sheaf CommRingCat.{u})
    (F G H : SheafOfModules.{u} (𝓡 S))
    {f g : (monoidalCategory S).tensorObj F G ⟶ H}
    (h : ∀ (W : (Opens Z)ᵒᵖ) (x : F.val.obj W) (y : G.val.obj W),
      f.val.app W ((tensorObjIsoSheafification F G).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (F.val ⊗ G.val)).app W (x ⊗ₜ[S.obj.obj W] y))) =
      g.val.app W ((tensorObjIsoSheafification F G).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)).unit.app
          (F.val ⊗ G.val)).app W (x ⊗ₜ[S.obj.obj W] y)))) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 S).obj)
  apply (cancel_epi (tensorObjIsoSheafification F G).inv).mp
  apply (adj.homEquiv (F.val ⊗ G.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h W x y

-- The mixed scalar structures require additional definitional equality checks.
/-- The map inserting `1` in the scalar-extension factor is invertible.
Source: Stacks Project, Cohomology, Tag 08DE, proof; Modules on Sites, Tag 0GMW.

Proof: let E be the presheaf U ↦ B(U) tensor_R(U) N(U). Before sheafification,
the balanced maps m tensor (b tensor n) ↦ (b m) tensor n and
m tensor n ↦ m tensor (1 tensor n) are inverse R(U)-linear maps. The balancing
relations prove well-definedness and tensor induction proves both inverse identities.
These maps commute with all restrictions because restriction preserves 1, products,
and scalar actions. Tensor with the sheafification of E is the sheafification of
tensor with E (Tag 0GMW). Forgetting module sheafification gives abelian sheafification,
independently of whether the coefficients are R or B. Thus the sectionwise inverse
maps induce inverse maps of abelian sheaves. The given formula identifies the
underlying map of φ with the inverse sectionwise map, by the tensor universal property
and uniqueness of sheafification. Hence its underlying map is an isomorphism.
The functor forgetting R-module structure reflects isomorphisms, so φ is invertible.
No flatness is used; zero rings, zero modules and the empty space are included.
(blueprint: lem-pc-balanced-sheaf-tensor-comparison-isIso) -/
theorem balancedTensorComparison_isIso (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R))
    (φ : (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N ⟶
      (restrictScalars (𝓻 α)).obj
        ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N)))
    (hφ : ∀ (W : (Opens Z)ᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      φ.val.app W
        ((tensorObjIsoSheafification ((restrictScalars (𝓻 α)).obj M) N).inv.val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app
            (((restrictScalars (𝓻 α)).obj M).val ⊗ N.val)).app W
              (m ⊗ₜ[R.obj.obj W] n))) =
      (tensorObjIsoSheafification M (changeOfRings.{u, u, u} α N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (M.val ⊗ (changeOfRings.{u, u, u} α N).val)).app W
            (m ⊗ₜ[B.obj.obj W]
              ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
                (changeOfRingsPresheaf.{u, u, u} α N)).app W
                  ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)))) :
    IsIso φ := by
  obtain ⟨ψ, hψ⟩ := exists_balancedTensorContraction α M N
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply tensor_sections_hom_ext R ((restrictScalars (𝓻 α)).obj M) N
    intro W m n
    change ψ.val.app W (φ.val.app W _) = _
    rw [hφ W m n, hψ W m 1 n]
    simp only [one_smul]
    rfl
  · apply balancedTensor_originalSections_hom_ext α M N
    intro W m b n
    change φ.val.app W (ψ.val.app W _) = _
    refine (congrArg (fun x ↦ φ.val.app W x) (hψ W m b n)).trans ?_
    refine (hφ W (b • m) n).trans ?_
    simp only [id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
    congr 1
    congr 1
    rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
    congr 1
    let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} α N)).app W
    change b • η ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n) =
      η (b ⊗ₜ[R.obj.obj W,(α.hom.app W).hom] n)
    let : CommRing ((𝓡 B).obj.obj W) :=
      inferInstanceAs (CommRing (B.obj.obj W))
    erw [← η.hom.map_smul]
    congr 1
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

end SheafOfModules
