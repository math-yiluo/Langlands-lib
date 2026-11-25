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
import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareComponent

/-! # Stalk compatibility of a specified tensor pullback chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-pinned-tensor-square-compatibility).
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

local instance pinnedTensorSquareCompatibilityT2Instance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y

local instance pinnedTensorSquareCompatibilityT2Instance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

attribute [local instance] pinnedTensorSquareLeftSummandInstance3
  pinnedTensorSquareLeftSummandInstance4

/-- Chain equation for the explicitly constructed pinned stalk tensor coordinates.

Proof: sigma and rho are the specific chain isomorphisms constructed from the
proved pinned stalk-total-tensor comparison, as displayed in the statement.
The inverse source comparison gives sigma. Tensor the inverse pullback-stalk
comparison on P with the identity on the stalk of N, then compose with the
inverse target comparison to obtain rho. These data come from proved existence
and canonical comparisons; the only deferred assertion here is their equation.
Check the chain equation degreewise after every total tensor summand injection.
The hypothesis hχ identifies the summand map with the specified module tensor
pullback comparison. The tensorStalkIso generator equation and the
module_pullback_tensor generator equation turn both composites on a pure tensor
into extension of its first factor to C followed by the stalk of a on its second
factor. The scalar-extension tensorator has the same pure-tensor formula.
Pure tensors generate each summand; the coproduct universal property then gives
equality in each total degree. Naturality of the stalk tensor and pullback
comparisons makes sigma and rho chain isomorphisms, including the differential
signs. Arbitrary direct sums, zero rings, zero factors and unbounded complexes
are included; no derived-category morphisms or K-flatness are used.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), Tag 0BYJ and
equation-bc before Tag 0DJ8; Cohomology, Tags 079R and 06YB.
(blueprint: lem-pc-pinned-tensor-square-compatibility). -/
theorem pinned_tensor_pullback_stalk_compatibility
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
          (curriedTensor _) (.up ℤ) p q n h) (z : X') :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
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
    F.map σ.hom ≫
          (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
            (pullbackTensorTotal X P Q)).hom ≫
          S.map (χ.hom ≫ HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ)) =
        (Functor.Monoidal.μIso F U V).inv ≫ (F.obj U ◁ t) ≫ ρ.hom := by
  apply HomologicalComplex.hom_ext
  intro n
  exact pinned_tensor_pullback_stalk_component f f' g g' sq P Q N a χ hχ z n

end AlgebraicGeometry
