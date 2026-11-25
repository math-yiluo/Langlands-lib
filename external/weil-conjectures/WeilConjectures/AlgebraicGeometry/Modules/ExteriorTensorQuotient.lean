/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# Exterior tensor quotients
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

-- Naturality compares exterior restrictions across the ring-sheaf module interfaces.
set_option backward.isDefEq.respectTransparency false in
/-- An epimorphism induces an epimorphism on a tensor of exterior sheaves. -/
theorem exteriorTensor_quotient_exists {X : Scheme.{v}} (A B C : X.Modules)
    (g : B ⟶ C) [Epi g] (r s : ℕ) :
    ∃ q : exteriorPower A r ⊗ exteriorPower B s ⟶
        exteriorPower A r ⊗ exteriorPower C s,
      Epi q ∧ ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        q.val.app (op U)
            (tmulSection (wedge (M := A) (r := r) (U := U) a)
              (wedge (M := B) (r := s) (U := U) c)) =
          tmulSection (M := exteriorPower A r) (N := exteriorPower C s)
            (wedge (M := A) (r := r) (U := U) a)
            (wedge (M := C) (r := s) (U := U) (fun i ↦ g.val.app (op U) (c i))) := by
  let p : B.val.exteriorPower (R := X.presheaf) s ⟶ C.val.exteriorPower (R := X.presheaf) s :=
    { app := fun U ↦ by
        let : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        exact ModuleCat.ofHom (_root_.exteriorPower.map s (g.val.app U).hom)
      naturality := by
        intro U V f
        let : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        let : CommRing (X.ringCatSheaf.obj.obj V) :=
          inferInstanceAs (CommRing (X.presheaf.obj V))
        apply ModuleCat.hom_ext
        apply _root_.exteriorPower.linearMap_ext (R := X.presheaf.obj U)
        apply AlternatingMap.ext
        intro c
        change _root_.exteriorPower.map s (g.val.app V).hom
            (((B.val.exteriorPower (R := X.presheaf) s).map f)
              (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c)) =
          ((C.val.exteriorPower (R := X.presheaf) s).map f)
            (_root_.exteriorPower.map s (g.val.app U).hom
              (_root_.exteriorPower.ιMulti (X.presheaf.obj U) s c))
        have hm :=
          (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) B.val s f) c
        have hn :=
          (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) C.val s f)
            (fun i ↦ g.val.app U (c i))
        have hu := _root_.exteriorPower.map_apply_ιMulti (R := X.presheaf.obj U) (n := s)
          (g.val.app U).hom c
        have hv := _root_.exteriorPower.map_apply_ιMulti (R := X.presheaf.obj V) (n := s)
          (g.val.app V).hom (fun i ↦ B.val.map f (c i))
        have ht : (fun i ↦ g.val.app V (B.val.map f (c i))) =
            (fun i ↦ C.val.map f (g.val.app U (c i))) := by
          funext i
          exact PresheafOfModules.naturality_apply g.val f (c i)
        exact (congrArg (_root_.exteriorPower.map (R := X.presheaf.obj V) s
          (g.val.app V).hom) hm).trans (hv.trans
            ((congrArg (_root_.exteriorPower.ιMulti (X.presheaf.obj V) s) ht).trans
              (hn.symm.trans
                (congrArg ((C.val.exteriorPower (R := X.presheaf) s).map f) hu).symm))) }
  let e : exteriorPower B s ⟶ exteriorPower C s :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p
  have he (U : X.Opens) (c : Fin s → B.val.obj (op U)) :
      e.val.app (op U) (wedge (M := B) (r := s) (U := U) c) =
        wedge (M := C) (r := s) (U := U) (fun i ↦ g.val.app (op U) (c i)) := by
    let : CommRing (X.ringCatSheaf.obj.obj (op U)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op U)))
    let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 X.ringCatSheaf.obj)
    have hn := congrArg (fun k ↦ k.app (op U)
      (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) s c)) (adj.unit.naturality p).symm
    change e.val.app (op U) (wedge (M := B) (r := s) (U := U) c) =
      (adj.unit.app (C.val.exteriorPower (R := X.presheaf) s)).app (op U)
        (_root_.exteriorPower.map s (g.val.app (op U)).hom
          (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) s c)) at hn
    exact hn.trans (congrArg ((adj.unit.app (C.val.exteriorPower (R := X.presheaf) s)).app (op U))
      (_root_.exteriorPower.map_apply_ιMulti (R := X.presheaf.obj (op U))
        (g.val.app (op U)).hom c))
  let q := (𝟙 (exteriorPower A r)) ⊗ₘ e
  have hq (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)) :
      q.val.app (op U)
          (tmulSection (wedge (M := A) (r := r) (U := U) a)
            (wedge (M := B) (r := s) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower C s)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := C) (r := s) (U := U) (fun i ↦ g.val.app (op U) (c i))) := by
    change ((𝟙 (exteriorPower A r)) ⊗ₘ e).app U _ = _
    rw [tensorHom_app_tmulSection]
    change tmulSection (M := exteriorPower A r) (N := exteriorPower C s)
      (wedge (M := A) (r := r) (U := U) a)
      (e.val.app (op U) (wedge (M := B) (r := s) (U := U) c)) = _
    rw [he]
  refine ⟨q, ?_, hq⟩
  constructor
  intro D φ ψ hcomp
  apply exteriorTensor_lift_hom_ext g r s
  intro U a c
  rw [← hq U a c]
  exact congrArg (fun k ↦ k.val.app (op U)
    (tmulSection (wedge (M := A) (r := r) (U := U) a)
      (wedge (M := B) (r := s) (U := U) c))) hcomp

end AlgebraicGeometry.Scheme.Modules
