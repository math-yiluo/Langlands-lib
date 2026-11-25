/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation

/-! # Natural structure-sheaf coordinates for tensor sections

Source: Stacks Project, Tags 0096, 01CA and 03DR.
(blueprint: lem-sc-etale-tensor-unit-sections-natural)
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules


local instance (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensor_unit_smul {A B : Scheme.{u}} (f : A ⟶ B) (r : Γ(B, ⊤)) :
    (tensorPullback f).map (smulHom (SheafOfModules.unit B.ringCatSheaf) r) ≫
        tensorPullbackObjUnitToUnit f =
      tensorPullbackObjUnitToUnit f ≫
        smulHom (SheafOfModules.unit A.ringCatSheaf) (f.appTop r) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  have he : adj.homEquiv _ _ (tensorPullbackObjUnitToUnit f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, he,
    pushforward_map_smulHom]
  exact smulHom_naturality _ r

private theorem unit_map_eval {A : Scheme.{u}} {M : A.Modules}
    (a : M ⟶ SheafOfModules.unit A.ringCatSheaf) (b : M ⟶ M) (r : Γ(A, ⊤))
    (h : b ≫ a = a ≫ smulHom (SheafOfModules.unit A.ringCatSheaf) r)
    (x : Γ(M, ⊤)) :
    (show Γ(A, ⊤) from a.app ⊤ (b.app ⊤ x)) =
      (show Γ(A, ⊤) from a.app ⊤ x) * r := by
  have he := congrArg (fun φ ↦ φ.app ⊤ x) h
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app_top_apply] at he
  change (show Γ(A, ⊤) from a.app ⊤ (b.app ⊤ x)) =
    r * (show Γ(A, ⊤) from a.app ⊤ x) at he
  exact he.trans (mul_comm _ _)

/-- The unit module's tensor sections have their usual structure-sheaf coordinates,
compatibly with restrictions and multiplication by global functions.
Source: Stacks Project, Tags 0096 and 01CA (pullback of the unit), and Tag 03DR,
equation (35.8.1) (normalized restrictions).
(blueprint: lem-sc-etale-tensor-unit-sections-natural)

Proof: For u:U -> X take the section map of the adjoint structure-sheaf morphism
u^* O_X -> O_U. It is an isomorphism by tensorPullbackObjUnitToUnit_isIso.
Its adjunction-unit equation identifies the image of a section r with u^*(r).
The unit equation for normalized composition then identifies restriction along
v:V -> U with the structure-sheaf restriction v^*. Hence the section isomorphisms
are natural. For multiplication by r, naturality of the adjunction gives the
commuting square between u^*(r times -) and multiplication by u^*(r) after the
unit isomorphism. Equivalently, evaluate the square on the unit generator and use
O_U-linearity: a section x maps to u^*(r) times its coordinate. Commutativity of
O_U gives the displayed order of factors. These arguments also hold on the empty
scheme and for r=0 or r=1; they impose no field or dimension hypothesis. -/
theorem exists_etaleTensorUnit_sections_natural (X : Scheme.{u}) :
    ∃ b : ∀ U : X.Etaleᵒᵖ,
        (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U ≃+
          Γ(U.unop.left, ⊤),
      (∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V)
          (x : (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U),
        b V ((etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.map g x) =
          g.unop.left.appTop (b U x)) ∧
      (∀ (r : Γ(X, ⊤))
          (θ : etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf) ⟶
            etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)),
        (∀ U : X.Etale, θ.hom.app (Opposite.op U) =
          ((tensorPullback U.hom).map (smulHom (SheafOfModules.unit X.ringCatSheaf) r)).app ⊤) →
        ∀ (U : X.Etaleᵒᵖ)
          (x : (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U),
          b U (θ.hom.app U x) =
            b U x * (show Γ(U.unop.left, ⊤) from U.unop.hom.appTop r)) := by
  classical
  have hi (U : X.Etaleᵒᵖ) : IsIso (tensorPullbackObjUnitToUnit U.unop.hom) :=
    (tensorPullbackObjUnitToUnit_isIso U.unop.hom).1
  let b : ∀ U : X.Etaleᵒᵖ,
      (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U ≃+
        Γ(U.unop.left, ⊤) := fun U ↦
    AddEquiv.ofBijective ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤).hom
      (ConcreteCategory.bijective_of_isIso
        ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤))
  refine ⟨b, ?_, ?_⟩
  · intro U V g x
    exact etaleTensorUnitRestriction_equation g.unop x
  · intro r θ hθ U x
    rw [hθ U.unop]
    exact unit_map_eval (tensorPullbackObjUnitToUnit U.unop.hom)
      ((tensorPullback U.unop.hom).map (smulHom (SheafOfModules.unit X.ringCatSheaf) r))
      (U.unop.hom.appTop r) (tensor_unit_smul U.unop.hom r) x

end AlgebraicGeometry.Scheme.Modules
