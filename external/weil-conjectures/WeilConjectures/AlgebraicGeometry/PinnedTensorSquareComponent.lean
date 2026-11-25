/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.PinnedStalkTensor
public import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareLeftSummand
import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareRightSummand

/-! # Stalk compatibility of a specified tensor pullback chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-pinned-tensor-square-component).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry

local instance pinnedTensorSquareComponentInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y

local instance pinnedTensorSquareComponentInstance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

attribute [local instance] pinnedTensorSquareLeftSummandInstance3
  pinnedTensorSquareLeftSummandInstance4

/-- Degreewise component equation for the explicitly constructed pinned stalk tensor coordinates.

Proof: the degree-n source is scalar extension of the coproduct of tensor summands
U.X p tensor V.X q for p+q=n. Scalar extension preserves this coproduct. Apply
mapBifunctor.hom_ext_of_map to its summand injections. On each summand, the left-route
and right-route calculation identify the two composites with the same explicit map:
the module tensorator followed by κ_P,p tensor κ_Q,q, identity tensor S(a)_q, the
injection into the target stalk tensor complex, and the inverse pinned comparison.
Transitivity proves the summand equality; coproduct extensionality proves the component
equality. The module generator calculation is used only by the left-route formula.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), degreewise generator calculation.
(blueprint: lem-pc-pinned-tensor-square-component). -/
theorem pinned_tensor_pullback_stalk_component
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    (a : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q ⟶ N)
    (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P Q) ≅
      pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q))
    (hχ : ∀ (p q n : ℤ) (h : p + q = n),
      (Scheme.Modules.tensorPullback g').map
          (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫
        χ.hom.f n =
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g')) (P.X p) (Q.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q)
          (curriedTensor _) (.up ℤ) p q n h) (z : X') (n : ℤ) :
    let := SingleComplexBaseChange.leftAlgebra f g' z
    let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    let := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let V := SingleComplexBaseChange.stalkComplex g' z Q
    let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom ≫ S.map a
    let H := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
    let e := Classical.choose (exists_pinned_stalk_tensor X (g' z))
    let e' := Classical.choose (exists_pinned_stalk_tensor X' z)
    let σ : U ⊗ V ≅ SingleComplexBaseChange.stalkComplex g' z
      (pullbackTensorTotal X P Q) := (e P Q).symm
    let ρ : F.obj U ⊗ S.obj N ≅ S.obj (pullbackTensorTotal X' (H.obj P) N) :=
      tensorIso (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z P)
        (Iso.refl (S.obj N)) ≪≫ (e' (H.obj P) N).symm
    (F.map σ.hom ≫
          (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
            (pullbackTensorTotal X P Q)).hom ≫
          S.map (χ.hom ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ))).f n =
        ((Functor.Monoidal.μIso F U V).inv ≫ (F.obj U ◁ t) ≫ ρ.hom).f n := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  let G := ModuleCat.extendScalars.{u, u, u}
    ((algebraMap (TensorProduct (SingleComplexBaseChange.R f g' z)
        (SingleComplexBaseChange.A g' z) (SingleComplexBaseChange.B f' z))
        (SingleComplexBaseChange.C z)).comp
      (algebraMap (SingleComplexBaseChange.A g' z)
        (TensorProduct (SingleComplexBaseChange.R f g' z)
          (SingleComplexBaseChange.A g' z) (SingleComplexBaseChange.B f' z))))
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map G
  intro p q h
  calc
    _ = _ := pinned_tensor_square_left_summand f f' g g' sq P Q N a χ hχ z n p q h
    _ = _ := (pinned_tensor_square_right_summand f f' g g' sq P Q N a z n p q h).symm


end AlgebraicGeometry
