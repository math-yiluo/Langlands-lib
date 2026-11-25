/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat

/-!
# K-flatness of pro-étale pullback of internal modules

Source: Stacks Project, Tags 0DEN and 0DEP.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

/-- Base change on the small pro-étale sites. Source: Stacks, Tag 09A5
(auxiliary; not a blueprint node). -/
private noncomputable abbrev proEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Continuity of the canonical base-change functor. Source: Stacks, Tag 09A5
(auxiliary; not a blueprint node). -/
private instance proEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleBaseChange f).IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
  ProEt.isContinuous_overPullback f

/-- Base change preserves finite limits. Source: Stacks, Tags 09A5 and 00X6
(auxiliary; not a blueprint node). -/
private instance proEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (proEtaleBaseChange f) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private noncomputable instance cachedSheafColimits (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  ⟨fun _ _ ↦ Sheaf.instHasColimitsOfShape⟩

private noncomputable instance cachedSheafBigColimits (T : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasColimits _

private noncomputable instance cachedCoequalizers (T : Scheme.{u}) :
    HasCoequalizers (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

private instance cachedModulePreadditive (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    MonoidalPreadditive (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedTensorLeft (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  infer_instance

private instance cachedTensorRight (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  infer_instance

private instance cachedGood12 (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P Q R₁ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q R₁ := by
  infer_instance

private instance cachedGood23 (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P Q R₁ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q R₁ := by
  infer_instance

private instance cachedFour (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P Q R₁ S₁ : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt P Q R₁ S₁ := by
  infer_instance

private instance countableTensor (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    TensorPreservesCountableCoproducts (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) where
  left _ _ _ := inferInstance
  right _ _ _ := inferInstance
private theorem section_kflat_iff (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) ℤ) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ↔
      CochainComplex.IsKFlatIndependentCoefficients
        ((((InternalAbelianSheafModule.sectionModuleEquivalence
          (Scheme.ProEt.topology T) R).functor).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨e, e₀, _, _, _, _, _, _, _, _, _, _, hk⟩ :=
    (InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology T) R).2
  exact (Equivalence.acyclic_tensor_iff_kFlat P).symm.trans
    ((Equivalence.acyclic_tensor_swap P).trans (hk P))


/-- Pullback preserves K-flat internal module complexes over every commutative
ring object. Source: Stacks Project, Tags 0DEN and 0DEP
(auxiliary; not a blueprint node).
Proof: compare internal modules with section modules, present inverse image by its
algebraic lift, and use stalkwise K-flatness at the enough family of pro-étale points.
The algebraic stalk functor at a point of the source is a stalk at the composite point
on the target. Transfer the result back through the section-module tensor comparison.
This argument also covers the zero ring, empty scheme and unbounded complexes. -/
theorem preservesKFlatComplexes_mapMod_proEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ((f)^*[Ab.{u + 1}].mapMod R).PreservesKFlatComplexes := by
  classical
  constructor
  intro P hP
  let F := (f)^*[Ab.{u + 1}].mapMod R
  let S := (f)^*[Ab.{u + 1}].obj R
  let EY := InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology Y) R
  let EX := InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X) S
  obtain ⟨I, ⟨θ⟩⟩ := exists_sectionModuleAlgebraicInverseImage f R S (𝟙 S)
  have : I.modules.Additive := Functor.additive_of_iso θ
  let geom : GeometricMorphism
      (Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
      (Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) :=
    -- `ProEtale.upperStar` needs an abelian Grothendieck coefficient category, so for
    -- `Type`-valued sheaves the inverse image is spelled out as in its definition.
    { inverse := Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.proEtaleBaseChange f)
        (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      direct := ProEtale.lowerStar (Type (u + 1)) f
      adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Scheme.proEtaleBaseChange f)
        (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      leftExact := by
        have : PreservesFiniteLimits
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.lan :
              (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) := by
          let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
            AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
          apply preservesFiniteLimits_op_lan_of_flat
        unfold Functor.sheafPullbackConstruction.sheafPullback
        infer_instance }
  obtain ⟨ι, p, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S) (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty _ (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro A B a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  have hPI := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) geom I ι p s hcons
    ((EY.functor.mapHomologicalComplex (.up ℤ)).obj P)
    ((section_kflat_iff Y R P).1 hP)
  let e₀ : Mod.mapModComap (𝟙 S) ≅ F :=
    Functor.isoWhiskerLeft F (Mod.comapId S) ≪≫ Functor.rightUnitor F
  let e : EY.functor ⋙ I.modules ≅ F ⋙ EX.functor :=
    Functor.isoWhiskerLeft EY.functor θ.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EY.unitIso.symm _ ≪≫ Functor.leftUnitor _ ≪≫
      Functor.isoWhiskerRight e₀ EX.functor
  let eP := (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app P
  have htarget : CochainComplex.IsKFlatIndependentCoefficients
      ((EX.functor.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
    let B := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S
    let := SheafOfModules.isMonoidal_W_independentCoefficients B
    let := SheafOfModules.monoidalCategory B
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients B
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients B
    intro A hA n
    exact (hPI A hA n).of_iso
      (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj A).mapIso
        (eP ≪≫ ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ EX.functor))
          (.up ℤ)).app P).symm))
  exact (section_kflat_iff X S _).2 htarget

end AlgebraicGeometry.ProEtale.CondensedRing
