/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Ordinary cycles of the pulled-back local model

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: def-sc-picard-ordinary-model-cycles)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Ordinary degree-zero cycles, with the source also pulled back from W.
The equivalence of the localized site with U is the existing `Modules.overEquiv`.
Source: Stacks Project, Tag 06YJ.
(blueprint: def-sc-picard-ordinary-model-cycles) -/
def picardOrdinaryModelCycles (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme) :
    AddSubgroup ((Modules.tensorPullback t).obj
      (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
        (Modules.tensorPullback s).obj ((Modules.overEquiv U).functor.obj (K.X 0))) :=
  AddMonoidHom.ker
    { toFun := fun f ↦ f ≫ (Modules.tensorPullback s).map
        ((Modules.overEquiv U).functor.map (K.d 0 1))
      map_zero' := by simp
      map_add' := fun f g ↦ by simp only [Preadditive.add_comp] }

/-- Pullback of a raw degree-zero morphism, conjugated by the two canonical
underived composition comparisons. Membership in the cycles subgroup is not
needed to define this map.
Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-picard-ordinary-model-cycles) -/
def picardOrdinaryModelRestriction (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
    (ht : i ≫ t = t') (hs : i ≫ s = s')
    (f : (Modules.tensorPullback t).obj
      (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
        (Modules.tensorPullback s).obj ((Modules.overEquiv U).functor.obj (K.X 0))) :
    (Modules.tensorPullback t').obj
      (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
        (Modules.tensorPullback s').obj ((Modules.overEquiv U).functor.obj (K.X 0)) :=
  ((conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction t)).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction t'))).symm
      (Modules.pushforwardComp i t ≪≫ Modules.pushforwardCongr ht)).hom.app _ ≫
    (Modules.tensorPullback i).map f ≫
      ((conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction s)).comp
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction s'))).symm
      (Modules.pushforwardComp i s ≪≫ Modules.pushforwardCongr hs)).inv.app _

end
end AlgebraicGeometry.Scheme
