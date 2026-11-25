/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower

/-!
# Exterior sheaf maps induced by module morphisms
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem restriction_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (k : U ⟶ V) (a : Fin n → M.val.obj U) :
    (M.val.exteriorPower (R := X.presheaf) n).map k
        (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n a) =
      (_root_.exteriorPower.ιMulti _ n (fun i ↦ M.val.map k (a i)) :
        (M.val.exteriorPower (R := X.presheaf) n).obj V) :=
  _root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) M.val n k a

-- Comparing scheme ring-sheaf scalar structures requires additional elaboration.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Apply the sectionwise exterior-power functor to a module morphism. Naturality is checked
on pure wedges using naturality of the original morphism; pure wedges span the exterior
power. Sheafify this presheaf morphism. Naturality of the sheafification unit gives its
formula on wedge sections. No exactness or local freeness is required. -/
theorem exteriorSheaf_map_exists {X : Scheme.{v}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    ∃ e : exteriorPower M n ⟶ exteriorPower N n,
      ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U)),
        e.val.app (op U) (wedge (M := M) (r := n) (U := U) a) =
          wedge (M := N) (r := n) (U := U) (fun i ↦ f.val.app (op U) (a i)) := by
  let p : (M.val.exteriorPower (R := X.presheaf) n) ⟶ (N.val.exteriorPower (R := X.presheaf) n) :=
    { app := fun U ↦ ModuleCat.ofHom (X := ((M.val.exteriorPower (R := X.presheaf) n).obj U))
        (Y := ((N.val.exteriorPower (R := X.presheaf) n).obj U))
        (_root_.exteriorPower.map (R := X.presheaf.obj U) n (f.val.app U).hom)
      naturality := by
        intro U V k
        apply ModuleCat.hom_ext
        apply _root_.exteriorPower.linearMap_ext (R := X.presheaf.obj U)
          (N := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map k).hom).obj
            (((N.val.exteriorPower (R := X.presheaf) n).obj V)))
        apply DFunLike.ext
        intro a
        symm
        change ((N.val.exteriorPower (R := X.presheaf) n).map k)
            (_root_.exteriorPower.map (R := X.presheaf.obj U) n (f.val.app U).hom
              (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n a)) =
          _root_.exteriorPower.map (R := X.presheaf.obj V) n (f.val.app V).hom
            (((M.val.exteriorPower (R := X.presheaf) n).map k)
              (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n a))
        rw [_root_.exteriorPower.map_apply_ιMulti (R := X.presheaf.obj U) (f.val.app U).hom a,
          restriction_wedge N n k, restriction_wedge M n k a]
        erw [_root_.exteriorPower.map_apply_ιMulti (R := X.presheaf.obj V)
          (f.val.app V).hom (fun i ↦ M.val.map k (a i))]
        apply congrArg (_root_.exteriorPower.ιMulti (X.presheaf.obj V) n)
        funext i
        exact (PresheafOfModules.naturality_apply f.val k (a i)).symm }
  refine ⟨(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p, ?_⟩
  intro U a
  have h := congrArg
    (fun k ↦ k.app (op U) (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality p)
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (N.val.exteriorPower (R := X.presheaf) n)).app (op U)
      (_root_.exteriorPower.map (R := X.presheaf.obj (op U)) n (f.val.app (op U)).hom
        (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)) =
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p).val.app (op U)
      (wedge (M := M) (r := n) (U := U) a) at h
  rw [_root_.exteriorPower.map_apply_ιMulti (R := X.presheaf.obj (op U))
    (f.val.app (op U)).hom a] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Modules
