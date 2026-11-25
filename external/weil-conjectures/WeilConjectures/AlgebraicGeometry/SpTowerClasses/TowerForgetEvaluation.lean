/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems

/-! # Additive evaluation for a recorded tower-forgetting functor

Source: blueprint sec-smooth-purity/sk-prop-sp-tower-geometric,
classes (2), underlying sheaves of ordinary systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private theorem transport_addHom {A B A' B' : AddCommGrpCat.{u + 1}}
    (eA : A = A') (eB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f.hom g.hom) :
    f ≫ eqToHom eB = eqToHom eA ≫ g := by
  subst A'
  subst B'
  have h' := eq_of_heq h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact AddCommGrpCat.hom_ext h'

private theorem transport_element {A B : AddCommGrpCat.{u + 1}} (e : A = B)
    (x : A) (y : B) (h : HEq x y) : (eqToHom e) x = y := by
  subst B
  exact eq_of_heq h

private def forgetEvaluationIso (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (M : Systems T B) (n : ℕ) :
    (F.F.obj M).obj (op n) ≅
      (SheafOfModules.toSheaf _).obj
        ((SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (fun n ↦ B.obj (op n))
          (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) n).obj M) := by
  let G : T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    (Prod.sectR n T.ProEt).op ⋙ M.val.presheaf
  let e₀ : ((F.F.obj M).obj (op n)).obj ≅ G := by
    refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · exact eqToIso (F.sections M n U)
    · intro U V f
      exact transport_addHom (F.sections M n U) (F.sections M n V) _ (G.map f)
        (F.restrictions M n f)
  exact ObjectProperty.isoMk _ e₀

private theorem forgetEvaluationIso_section (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (M : Systems T B) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop)))
    (x' : ((F.F.obj M).obj (op n)).obj.obj U) (hx : HEq x x') :
    (forgetEvaluationIso T B F M n).hom.hom.app U x' = x := by
  change (eqToHom (F.sections M n U)) x' = x
  exact transport_element (F.sections M n U) x' x hx.symm

/-- A recorded tower identification agrees with additive module evaluation.
Source: blueprint classes (2), the section and restriction equations of Forget.
(blueprint: lem-sp-tower-forget-evaluation).

Proof: the equations F.sections give identity-transport isomorphisms at each
object, natural by F.restrictions. Lift them to a sheaf isomorphism and compose
with the inverse of h at n. On a section in the image of h, its inverse cancels h;
transport by F.sections then sends the forgotten section to its HEq representative. -/
theorem forget_evaluation_iso (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (M : Systems T B) (n : ℕ)
    (G : Ab T) (h : F.F.obj M ≅ G) :
    ∃ e : G.obj (op n) ≅
      (SheafOfModules.toSheaf _).obj
        ((SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (fun n ↦ B.obj (op n))
          (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) n).obj M),
      ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop)))
        (x' : ((F.F.obj M).obj (op n)).obj.obj U),
        HEq x x' → e.hom.hom.app U (((h.hom.app (op n)).hom.app U) x') = x := by
  let e := (h.app (op n)).symm ≪≫ forgetEvaluationIso T B F M n
  refine ⟨e, ?_⟩
  intro U x x' hx
  change (forgetEvaluationIso T B F M n).hom.hom.app U
    (((h.inv.app (op n)).hom.app U) (((h.hom.app (op n)).hom.app U) x')) = x
  have hi := congrArg (fun q ↦ q.hom.app U x') (h.app (op n)).hom_inv_id
  change ((h.inv.app (op n)).hom.app U) (((h.hom.app (op n)).hom.app U) x') = x' at hi
  rw [hi]
  exact forgetEvaluationIso_section T B F M n U x x' hx

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
