/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.ULift

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An abelian sheaf killed by `n` has a lift to sheaves of `ULift (ZMod n)`-modules.

Source: Stacks Project, Tag 095T, passage to Z/ell-module sheaves, and the sectionwise
construction implicit in Tag 03RW; Mathlib `AddCommGroup.zmodModule`.
(blueprint: lem-weil-pbc-killed-sheaf-module-lift)

Proof: evaluate `n • id = 0` at each object and section. The section groups therefore
carry the canonical Z/n-action, with a lifted scalar acting by its underlying residue.
Every restriction is additive, hence Z/n-linear. This gives a module presheaf. Its
underlying presheaf of abelian groups is the original one, so it is a sheaf because the
forgetful functor reflects limits. The identity maps give the underlying sheaf
isomorphism. This also works for n = 0 (the integer action), n = 1 (the zero sheaf),
and the zero sheaf for any n. -/
theorem exists_module_sheaf_of_nsmul_id_eq_zero (X : Scheme.{u}) (n : ℕ)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : n • 𝟙 G = 0) :
    ∃ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))),
      Nonempty (((sheafCompose _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
          AddCommGrpCat.{u + 1})).obj M) ≅ G) := by
  have hkill (U : X.Etaleᵒᵖ) (x : G.obj.obj U) : n • x = 0 := by
    have h := congrArg (fun f : G ⟶ G ↦ f.hom.app U x) hG
    change ((n • (𝟙 (G.obj.obj U))).hom) x = 0 at h
    simpa using h
  let (U : X.Etaleᵒᵖ) : Module (ZMod n) (G.obj.obj U) :=
    AddCommGroup.zmodModule (hkill U)
  let P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)) :=
    { obj := fun U ↦ ModuleCat.of _ (G.obj.obj U)
      map := fun f ↦ ModuleCat.ofHom
        { toFun := G.obj.map f
          map_add' := map_add (G.obj.map f).hom
          map_smul' := fun c x ↦ ZMod.map_smul (G.obj.map f).hom c.down x }
      map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (G.obj.map_id U) x
      map_comp := fun f g ↦ by ext x; exact ConcreteCategory.congr_hom (G.obj.map_comp f g) x }
  have hP : Presheaf.IsSheaf X.smallEtaleTopology P := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})
    exact G.property
  refine ⟨⟨P, hP⟩, ⟨?_⟩⟩
  exact Iso.refl G

end AlgebraicGeometry
