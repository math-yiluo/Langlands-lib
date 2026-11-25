/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.Topology.Homeomorph.Defs
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Canonical trivialization of absolute Frobenius on the small pro-etale site

All constant commutative coefficient rings are allowed. The module adjunction unit,
evaluated on every section, fixes the trivialization; its derived version is exact
termwise descent. The comparisons in the compatibility equations are fixed by
fibre-product pasting and conjugation, not independently chosen isomorphisms.

## References

* Stacks Project, Tag 0F6W
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Elaborate the dependent section APIs in declaration order.
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModuleAdjunction
  proEtaleRingModulePullback proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap

-- Keep the adjunction-defined coefficient map behind its constant-section API.
private noncomputable def coefficientDirectMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A) :=
  proEtaleCoefficientDirectImageMap f A

private theorem constantSection_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
      (coefficientDirectMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange f).op.obj W) := by
  unfold coefficientDirectMap
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))
  exact congrArg (fun t ↦ t.app W) h

private theorem constantRing_direct
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap f A)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (asIso (proEtaleCoefficientInverseImageMap f A)) =
        coefficientDirectMap f A := by
  unfold coefficientDirectMap
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (coefficientDirectMap f A)

attribute [local irreducible] coefficientDirectMap
  proEtaleRingDirectImageMap proEtaleConstantRingComparison

private noncomputable def moduleRho {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A) ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A)) :=
  ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A)).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

set_option backward.isDefEq.respectTransparency false in
private theorem rho_trivialization (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    coefficientDirectMap f A ≫
      (Functor.sheafPushforwardContinuousNatTrans r.hom CommRingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology X)).app (proEtaleConstantRing X A) = 𝟙 _ := by
  apply (sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext W
  change _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, constantSection_unit]
  have hn := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).naturality
      (r.hom.app W.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  change (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
      ((proEtaleBaseChange f).op.obj W) ≫
    (proEtaleConstantRing X A).obj.map (r.hom.app W.unop).op =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫ 𝟙 _
  rw [Category.comp_id]
  exact hn.symm.trans (Category.id_comp _)

private theorem moduleRho_trivialization (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    moduleRho f A ≫
      (Functor.sheafPushforwardContinuousNatTrans r.hom RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology X)).app
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing X A)) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  simp only [moduleRho, proEtaleConstantRingComparison, constantRing_direct]
  exact congrArg
    (fun h ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (h.hom.app W))
    (rho_trivialization A X f r)

attribute [local irreducible] CategoryTheory.constantSheaf

private noncomputable def constantPushforwardIso (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    proEtaleConstantRingPushforward A f ≅ 𝟭 _ :=
  SheafOfModules.pushforwardCongr₂ (moduleRho f A) r
    (moduleRho_trivialization A X f r) ≪≫ SheafOfModules.pushforwardId _

private noncomputable def constantPullbackIso (A : Type u) [CommRing A]
    (X : Scheme.{u}) (f : X ⟶ X) (r : 𝟭 X.ProEt ≅ proEtaleBaseChange f) :
    proEtaleConstantRingPullback A f ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (proEtaleConstantRingAdjunction A f)).symm
    (constantPushforwardIso A X f r).symm

attribute [local irreducible] constantPushforwardIso constantPullbackIso

attribute [local irreducible] iterateFrobenius

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] conjugateIsoEquiv conjugateEquiv

section RingedProduct

universe uC vC uR vM
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{uR}} {F G H : C ⥤ C}
variable [F.IsContinuous J J] [G.IsContinuous J J] [H.IsContinuous J J]
variable (φF : R ⟶ (F.sheafPushforwardContinuous RingCat J J).obj R)
variable (φG : R ⟶ (G.sheafPushforwardContinuous RingCat J J).obj R)
variable (φH : R ⟶ (H.sheafPushforwardContinuous RingCat J J).obj R)

end RingedProduct

-- Forget scalars before comparing the composite direct-image normalization.
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso

end AlgebraicGeometry.Scheme
