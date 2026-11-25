/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine evaluation of quasi-coherent module colimits

Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24, item (4).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections preserve a colimit whose stages and point are quasi-coherent on Spec R. -/
private theorem specModuleColimitEvaluation
    (R : CommRingCat.{u}) (I : Type u) [Category.{u} I]
    (F : I ⥤ (Spec R).Modules) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i : I, (F.obj i).IsQuasicoherent) (hq : c.pt.IsQuasicoherent) :
    Nonempty (IsColimit ((moduleSpecΓFunctor (R := R)).mapCocone c)) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F' : I ⥤ P.FullSubcategory := P.lift F hF
  let c' : Cocone F' :=
    { pt := ⟨c.pt, hq⟩
      ι := { app := fun i ↦ ObjectProperty.homMk (c.ι.app i)
             naturality := fun i j f ↦ ObjectProperty.hom_ext _ (c.w f) } }
  have hc' : IsColimit c' := isColimitOfReflects P.ι hc
  exact ⟨isColimitOfPreserves (tildeEquiv (R := R)).inverse hc'⟩

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the spectrum of an affine open computes evaluation on that open. -/
private noncomputable def affineEvaluationIso
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor (R := Γ(X, U)) ≅
      SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U) := by
  have he : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let e := M.restrictAppIso hU.fromSpec ⊤ ≪≫
      M.presheaf.mapIso (eqToIso he.symm).op
    let l : (moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) ≃ₗ[Γ(X, U)]
        (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)).obj M :=
      { toFun := e.hom
        invFun := e.inv
        left_inv := fun x ↦ Iso.hom_inv_id_apply e x
        right_inv := fun x ↦ Iso.inv_hom_id_apply e x
        map_add' := fun x y ↦ e.hom.hom.map_add x y
        map_smul' := fun r x ↦ by
          dsimp [e]
          rw [restrictAppIso_fromSpec_smul]
          change M.presheaf.map (eqToHom he.symm).op
            (X.presheaf.map (homOfLE (hU.fromSpec_image_le ⊤)).op r • _) = _
          rw [M.map_smul]
          simp [← Functor.map_comp_apply] }
    exact l.toModuleIso
  · intro M N f
    ext x
    change N.presheaf.map (eqToHom he.symm).op (f.app _ x) =
      f.app U (M.presheaf.map (eqToHom he.symm).op x)
    exact (ConcreteCategory.congr_hom
      (f.mapPresheaf.naturality (eqToHom he.symm).op) x).symm

/-- Evaluation on an affine open sends a quasi-coherent module colimit cocone to
an actual colimit cocone of modules. No filteredness is needed.
Source: Stacks Project, Schemes, Lemma 01ID and Lemma 01I7
(blueprint: lem-weil-pbc-quasi-coherent-module-colimit-evaluation).

Proof: Put R = Γ(X, U) and restrict the diagram and cocone along the open immersion
Spec R → X furnished by the affine open U. Restriction preserves colimits since it
is left adjoint to pushforward, and preserves quasi-coherence. The tilde-Gamma counit
identifies every restricted stage with the tilde of its global sections, naturally in
stage maps. The assumption that c.pt is quasi-coherent also lets one compute the
affine colimit in the full subcategory of quasi-coherent modules using tildeEquiv.
Form the colimit M of the section modules. The tilde functor is a left
adjoint, so tilde M is the colimit of the tilde stage modules. Uniqueness of colimits
gives an isomorphism tilde M ≅ c.pt restricted to Spec R, intertwining the legs.
Taking global sections and composing with the tilde-Gamma unit (an isomorphism)
gives M ≅ Γ(c.pt, U). Naturality of the unit and the triangle identity show that the
transported legs are precisely the original evaluated c.ι. Transport the module
colimit along this isomorphism. This works also for an empty indexing category,
where M is zero, and for the empty affine open, where every module is zero. -/
theorem quasiCoherentModuleColimitEvaluation
    (X : Scheme.{u}) (I : Type u) [Category.{u} I]
    (F : I ⥤ X.Modules) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i : I, (F.obj i).IsQuasicoherent) (hq : c.pt.IsQuasicoherent)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Nonempty (IsColimit
      ((SheafOfModules.evaluation (R := X.ringCatSheaf) (Opposite.op U)).mapCocone c)) := by
  obtain ⟨h⟩ := specModuleColimitEvaluation Γ(X, U) I
    (F ⋙ restrictFunctor hU.fromSpec) ((restrictFunctor hU.fromSpec).mapCocone c)
    (isColimitOfPreserves (restrictFunctor hU.fromSpec) hc)
    (fun i ↦ @isQuasicoherent_restrictFunctor _ _ hU.fromSpec _ (F.obj i) (hF i))
    (@isQuasicoherent_restrictFunctor _ _ hU.fromSpec _ c.pt hq)
  exact ⟨IsColimit.mapCoconeEquiv (affineEvaluationIso X U hU) h⟩

end AlgebraicGeometry.Scheme.Modules
