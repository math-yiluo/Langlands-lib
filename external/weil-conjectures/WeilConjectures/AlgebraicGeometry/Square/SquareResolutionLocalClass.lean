/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
import WeilConjectures.AlgebraicGeometry.Direct.DirectImageComplexLocalClass
import WeilConjectures.CategoryTheory.ProperBaseChange.TotalClassicalResolutionComparison

/-! # Agreement of classical resolution classes and derived local classes

Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-square-resolution-local-class).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
private theorem map_resolution_comparison
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D)
    {A B C' D' E F : C} {a : A ⟶ B} {b : B ⟶ C'}
    {c : C' ⟶ D'} {d : D' ⟶ E} {e : E ⟶ F} {k : A ⟶ F}
    (h : k = a ≫ b ≫ (c ≫ d) ≫ e) :
    S.map k = S.map (a ≫ b ≫ c ≫ d) ≫ S.map e := by
  rw [h, ← S.map_comp]
  congr 1
  simp only [Category.assoc]

private theorem local_class_paste
    {C : Type*} [Category C] {A B C' D E F G H I J K L M : C}
    {p : A ⟶ B} {p' : B ⟶ C'} {p'' : C' ⟶ D}
    {x : D ⟶ E} {y : E ⟶ F} {c₁ : D ⟶ G} {c₂ : G ⟶ H}
    {c₃ : H ⟶ I} {c₄ : I ⟶ J} {c₅ : J ⟶ K} {t : K ⟶ L}
    {d : L ⟶ F} {j : F ⟶ M} {k : L ⟶ M}
    (hc : x ≫ y = ((c₁ ≫ c₂ ≫ c₃) ≫ c₄ ≫ c₅) ≫ t ≫ d)
    (hd : k = d ≫ j) :
    (p ≫ p' ≫ p'' ≫ x ≫ y) ≫ j =
      ((p ≫ p' ≫ p'' ≫ c₁ ≫ c₂) ≫ c₃ ≫ c₄ ≫ c₅) ≫ t ≫ k := by
  rw [hd]
  simp only [Category.assoc] at hc ⊢
  rw [← Category.assoc x y j, hc]
  simp only [Category.assoc]

namespace AlgebraicGeometry
open Scheme.Modules
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Agreement of classical resolution classes and derived local classes.
Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X
(blueprint: lem-weil-pbc-square-resolution-local-class).

Proof: Compute total and classical right-derived cohomology on the same integer extension of I.
Uniqueness of derived units and the total/plus compatibility identify the cohomology comparison
with isoRightDerivedObj. Transport the section computation along the augmentation-preserving
restricted-resolution comparison.

On that representative, the underlying abelian module-sheafification unit and the abelian
sheafification unit both send a cocycle to its cohomology-sheaf class. Their exact homology
comparisons agree by naturality of the cycle and boundary quotients and their counits. Transport
through the normalized local Leray and sheafification comparisons and the comparisons of the first
step. This is the displayed equality; the equality of opens contributes just the indicated
transport. -/
theorem squareResolution_localClass {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (q : ℕ) (V : Y.Opens) (I : InjectiveResolution F)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U) :
    resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V (R.sections ≪≫ eqToIso (congrArg (fun W ↦
          ((RingedSpace.openModuleSections X.toRingedSpace W).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) hU)) q ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V =
    (squareLocalResolutionComparison f F q V I U hU R).hom ≫
      (RingedSpace.topEdgeLocalClass Y.toRingedSpace (q : ℤ)
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))).app (op V) ≫
      Hom.app (schemeSingleCohomologyComparison f F q).hom V := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  subst U
  let : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let r : (DerivedCategory.singleFunctor X.Modules 0).obj F ≅
      DerivedCategory.Q.obj I.cochainComplex :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫ asIso (DerivedCategory.Q.map I.ι')
  have hkinj : CochainComplex.IsKInjective (I.cocomplex.extend
      ComplexShape.embeddingUpNat) := by
    change I.cochainComplex.IsKInjective
    infer_instance
  have hc := @directImageComplex_localClass.{u, w} _ X Y f I.cocomplex hkinj _ r q V
  have hd := (pushforward f).totalClassicalResolutionComparison F I q
  dsimp only at hc hd
  dsimp only [InjectiveResolution.isoRightDerivedObjCochainComplex,
    Iso.trans, Iso.symm, Functor.mapIso, Iso.app] at hd
  have hκ := map_resolution_comparison
    (RingedSpace.openModuleSections Y.toRingedSpace V) hd
  unfold resolutionSectionClass squareLocalResolutionComparison
  dsimp only [r, Iso.trans, Iso.symm, Functor.mapIso, Iso.app] at hc ⊢
  exact local_class_paste hc hκ

end AlgebraicGeometry
