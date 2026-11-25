/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import WeilConjectures.AlgebraicGeometry.Modules.AffineDescent
import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
/-! # Tensoring frames under monoidal pullback
Source: Stacks Project, Tags 0095 and 0096, tensor pullback coherence.
(blueprint: lem-pur-tensor-pullback-frames). -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' u'' v''
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor two pulled-back frames using the monoidal comparison.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames). -/
def tensorPullbackFrames {T : Scheme.{u}} (L M : T.Modules)
    {X : Scheme.{u}} (f : X ⟶ T)
    (x : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj L)
    (y : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj M) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj (L ⊗ M) :=
  (Scheme.Modules.pullback f).map (λ_ (Scheme.Modules.unit T)).inv ≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
      (Scheme.Modules.unit T) (Scheme.Modules.unit T)).inv ≫
        (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L M).hom
private lemma scalar_natural {X : Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) (r : Γ(X, ⊤)) :
    Scheme.Modules.smulHom A r ≫ f = f ≫ Scheme.Modules.smulHom B r := by
  ext U x
  exact Scheme.Modules.Hom.app_smul f _ _

instance {T X : Scheme.{u}} (L M : T.Modules) (f : X ⟶ T)
    (x : (pullback f).obj (unit T) ⟶ (pullback f).obj L)
    (y : (pullback f).obj (unit T) ⟶ (pullback f).obj M) [IsIso x] [IsIso y] :
    IsIso (tensorPullbackFrames L M f x y) := by
  unfold tensorPullbackFrames
  infer_instance

private theorem presheafHom_map_eq {T : Scheme.{u}} (L M : T.Modules)
    {A B : Over T} (f : B ⟶ A)
    (x : (pullback A.hom).obj L ⟶ (pullback A.hom).obj M) :
    (modulesPseudofunctor.presheafHom L M).map f.op x =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulesPseudofunctor)
        (f₁ := A.hom) (f₂ := A.hom) x f.left B.hom B.hom
        (Over.w f) (Over.w f) := by
  simp only [Pseudofunctor.presheafHom_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]

/-- Restricting a pulled-back global map gives its pullback on the smaller object.
Source: Stacks 01CD (blueprint: lem-pur-tensor-pullback-frames).
Proof: use the pseudofunctor restriction formula on a mapped global morphism. -/
theorem pullbackMap_presheaf_map {T : Scheme.{u}} (L M : T.Modules)
    {A B : Over T} (f : B ⟶ A) (s : L ⟶ M) :
    (modulesPseudofunctor.presheafHom L M).map f.op ((pullback A.hom).map s) =
      (pullback B.hom).map s := by
  rw [presheafHom_map_eq]
  exact Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map
    (F := modulesPseudofunctor) s A.hom f.left B.hom (Over.w f)

attribute [irreducible] tensorPullbackFrames

end AlgebraicGeometry.Scheme.Modules
