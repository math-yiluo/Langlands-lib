/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLinePresentationDefs
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Mathlib.CategoryTheory.Subfunctor.Image
import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLinePresentationDefs

/-!
# Scheme-test presentations for a line module and its graded sections

Source: Stacks Project, Properties of Spaces, Tag 03G7; Divisors on Spaces, Tag 0D2Z;
and Constructions, Tag 01O9 (blueprint: def-trf-space-line-module-proj-input).

A cartesian family specifies the actual tensor pullbacks to schemes. Its identification
on the small etale site identifies the family with the given line module, rather than
introducing an unrelated line bundle. Graded maps are specified on homogeneous sections
on affine opens of the base, with scalar, product, unit, and restriction equations.

## Main definitions

* `EtaleLinePresentation` and `lineTestFamily` realize the given small-etale line module.
* `GradedLineMap` specifies the homogeneous algebra map on the actual scheme pullbacks.
* `GradedLineMap.IsGenerationOpen` specifies its positive-degree generation open.
* `GradedLineMap.IsCanonicalMap` specifies the usual local relative-Proj construction.
* `GradedLineMap.IsBaseChange` specifies the coefficientwise pulled-back graded map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A graded algebra map to tensor powers of the line module, written on homogeneous
sections of affine base charts. The linearity and naturality equations are the adjoint
form of a map from tensor pullback of the graded algebra sheaf.
Source: Stacks, Tags 0D2Z and 01O9
(blueprint: def-trf-space-line-module-proj-input). -/
structure GradedLineMap {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (A : T.left.GradedAlgebraData) (L : TestLineFamily F) where
  component (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1) (n : ℕ) :
    A.grading V n →+ Γ((L.module W).tensorPow n, ⊤)
  smul (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (n : ℕ) (r : Γ(T.left, V.1)) (a : A.grading V n) :
    component W V h n (r • a) =
      ((testToBase f W).left.appLE V.1 ⊤ h r) • component W V h n a
  one (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1) :
    component W V h 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      Scheme.Modules.unitSectionsEquiv ⊤ 1
  mul (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    component W V h (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      ((L.module W).tensorPowAddIso m n).inv.app ⊤
        (Scheme.Modules.tmulSection (component W V h m a) (component W V h n b))
  naturality {W W' : SchemeTests F} (j : W ⟶ W') (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (h' : (⊤ : W'.left.left.Opens) ≤ (testToBase f W').left ⁻¹ᵁ V.1)
      (n : ℕ) (a : A.grading V n) :
    component W V h n a = L.powerMap j n (component W' V h' n a)
  restriction (W : SchemeTests F) (V V' : T.left.affineOpens) (j : V ≤ V')
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (h' : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V'.1)
      (n : ℕ) (a : A.grading V' n) :
    component W V h n ⟨A.res j a, (A.res j).map_mem a.property⟩ =
      component W V' h' n a

/-- Tensor powers of a chosen trivialization, including the prescribed degree-zero unit.
Source: Stacks, Tag 01O9 (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def trivializedPower {W : Scheme.{u}} {L : W.Modules}
    (e : L ≅ SheafOfModules.unit W.ringCatSheaf) :
    (n : ℕ) → L.tensorPow n ≅ SheafOfModules.unit W.ringCatSheaf
  | 0 => Iso.refl _
  | n + 1 => (e ⊗ᵢ trivializedPower e n) ≪≫ λ_ _

/-- The relative Proj as an object over `S`, using its actual structural map.
Source: Stacks, Tags 01LH and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def projOver (T : Over S) (A : T.left.GradedAlgebraData) : Over S :=
  Over.mk (A.relProjHom ≫ T.hom)

/-- The canonical Proj map is characterized on all trivializing scheme charts by the
usual homogeneous-fraction construction. The ring homomorphism is required to agree
on every homogeneous section; consequently it is completely specified by `ψ` and `e`.
Source: Stacks, Tags 0D2Z(2) and 01O9
(blueprint: def-trf-space-line-module-proj-input). -/
def GradedLineMap.IsCanonicalMap {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    {f : F ⟶ yoneda.obj T} {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (U : Subfunctor F)
    (r : U.toFunctor ⟶ yoneda.obj (projOver T A)) : Prop :=
  (∀ (W : Over S) (a : U.toFunctor.obj (op W)),
    (r.app (op W) a).left ≫ A.relProjHom =
      (testToBase f (CostructuredArrow.mk (yonedaEquiv.symm a.val))).left) ∧
    ∀ (W : Over S) (a : U.toFunctor.obj (op W)) (V : T.left.affineOpens)
      (h : (⊤ : W.left.Opens) ≤
        (testToBase f (CostructuredArrow.mk (yonedaEquiv.symm a.val))).left ⁻¹ᵁ V.1)
      (e : L.module (CostructuredArrow.mk (yonedaEquiv.symm a.val)) ≅
        SheafOfModules.unit W.left.ringCatSheaf) (α : A.obj V →+* Γ(W.left, ⊤)),
      (∀ (n : ℕ) (b : A.grading V n), α b =
        (Scheme.Modules.unitSectionsEquiv ⊤).symm
          ((trivializedPower e n).hom.app ⊤
            (ψ.component (CostructuredArrow.mk (yonedaEquiv.symm a.val)) V h n b))) →
      ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤,
        (r.app (op W) a).left =
          Proj.fromOfGlobalSections (A.grading V) α hα ≫ A.relProjι V

end AlgebraicGeometry.AlgebraicSpace
