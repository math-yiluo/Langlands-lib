/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelFreeModule
public import WeilConjectures.AlgebraicGeometry.PointModelPullbackFunctor
public import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import WeilConjectures.AlgebraicGeometry.ConstantSliceInternalPresentation
import WeilConjectures.AlgebraicGeometry.DiscreteInternalMatrixLocalLifting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Lifting one discrete constant presentation

Source: Stacks, Tags 03CY, 00YV and 09AJ.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

-- Keep the functors abstract during the cokernel calculation. This avoids unfolding
-- their Kan extensions and scalar restrictions in the finite-colimit argument.
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  upperStar lowerStar CondensedRing.lowerStar CategoryTheory.Sheaf.monoidalCategory
  CondensedRing.upperStarComp upperStarFromPointComp Mod.extendScalarsIsoComapInv
  laxBraided_upperStarFromPoint monoidal_upperStarFromPoint
  smallModules coefficientModelFixedScalars Scheme.coefficientProEtaleFixedModulePullback
  pointModelFree pointModelRestriction pointModelPullbackFunctor

private theorem pointPullback_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    PreservesFiniteColimits (pointModelPullbackFunctor Λ Z) := by
  have : (upperStarFromPoint Z).IsLeftAdjoint := by
    unfold upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))).isLeftAdjoint
  unfold pointModelPullbackFunctor
  infer_instance

private noncomputable def cokernelIsoOfArrowIso
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y X' Y' : C} {a : X ⟶ Y} {b : X' ⟶ Y'}
    [HasCokernel a] [HasCokernel b] (e : Arrow.mk a ≅ Arrow.mk b) :
    cokernel a ≅ cokernel b :=
  cokernel.mapIso _ _ (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) e.hom.w.symm

private noncomputable def mappedCokernelIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (G : C ⥤ E) (P : D ⥤ E) [G.PreservesZeroMorphisms] [P.PreservesZeroMorphisms]
    {X Y : C} (a : X ⟶ Y) {X' Y' : D} (d : X' ⟶ Y')
    [HasCokernel a] [HasCokernel d] [HasCokernel (G.map a)] [HasCokernel (P.map d)]
    [PreservesColimit (parallelPair a 0) G] [PreservesColimit (parallelPair d 0) P]
    (i : Arrow.mk (G.map a) ≅ Arrow.mk (P.map d)) :
    G.obj (cokernel a) ≅ P.obj (cokernel d) :=
  PreservesCokernel.iso G a ≪≫ cokernelIsoOfArrowIso i ≪≫
    (PreservesCokernel.iso P d).symm

private noncomputable def restrictionCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z W : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Z ⟶ Y) (b : W ⟶ Z) :
    pointModelRestriction Λ f N (b ≫ g) ≅
      (CondensedRing.upperStar Λ b).obj (pointModelRestriction Λ f N g) := by
  unfold pointModelRestriction
  exact (CondensedRing.upperStarCongr Λ (Category.assoc b g f)).app N ≪≫
    (CondensedRing.upperStarComp Λ b (g ≫ f)).app N

private noncomputable def restrictionCongrIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {g g' : Z ⟶ Y} (h : g = g') :
    pointModelRestriction Λ f N g ≅ pointModelRestriction Λ f N g' :=
  eqToIso (congrArg (fun t ↦ pointModelRestriction Λ f N t) h)

private noncomputable def restrictionTriangleIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z W : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Z ⟶ Y) (b : W ⟶ Z) (v : W ⟶ Y) (h : b ≫ g = v) :
    pointModelRestriction Λ f N v ≅
      (CondensedRing.upperStar Λ b).obj (pointModelRestriction Λ f N g) :=
  restrictionCongrIso Λ f N h.symm ≪≫ restrictionCompIso Λ f N g b

private noncomputable def restrictionOverIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {U V : Y.ProEt} (g : V ⟶ U) :
    pointModelRestriction Λ f N V.hom ≅
      (CondensedRing.upperStar Λ g.left).obj
        (pointModelRestriction Λ f N U.hom) := by
  -- Infer these schemes from their underlying objects, not the comma identity functor.
  exact restrictionTriangleIso Λ (Z := U.left) (W := V.left) f N U.hom g.left V.hom
    (MorphismProperty.Over.w g)

private theorem presentation_of_local_matrix
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (m n : ℕ)
    (a : Mod.finiteFree (condensedRingObj Λ (AsSmall.down.obj U).left) m ⟶
      Mod.finiteFree (condensedRingObj Λ (AsSmall.down.obj U).left) n)
    (hN : Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅ cokernel a))
    (hmat : ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
      ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
        ∃ d : pointModelFree Λ m ⟶ pointModelFree Λ n,
          Nonempty
            (Arrow.mk ((CondensedRing.upperStar Λ (AsSmall.down.map g).left).map a) ≅
              Arrow.mk ((pointModelPullbackFunctor Λ (AsSmall.down.obj V).left).map d))) :
    ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
      ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
        ∃ d : pointModelFree Λ m ⟶ pointModelFree Λ n,
          Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj V).hom ≅
            (pointModelPullbackFunctor Λ (AsSmall.down.obj V).left).obj (cokernel d)) := by
  classical
  obtain ⟨iN⟩ := hN
  obtain ⟨S, hS, hs⟩ := hmat
  refine ⟨S, hS, ?_⟩
  intro V g hg
  obtain ⟨d, ⟨i⟩⟩ := hs V g hg
  let G := CondensedRing.upperStar Λ (AsSmall.down.map g).left
  let P := pointModelPullbackFunctor Λ (AsSmall.down.obj V).left
  have hG : PreservesFiniteColimits G := by unfold G; infer_instance
  have hP : PreservesFiniteColimits P := pointPullback_preservesFiniteColimits Λ _
  exact ⟨d, ⟨restrictionOverIso Λ f N (AsSmall.down.map g) ≪≫ G.mapIso iN ≪≫
    mappedCokernelIso G P a d i⟩⟩

/-- One specified finitely presented constant module on a slice lifts locally to finite
presentations on the condensed point. This concerns one constant module and its given
trivialization, before any locally constant predicate or covering family is assembled.

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV;
the reverse finite-matrix argument in lem-sfb-discrete-coefficient-local-models, steps 1--2.
(auxiliary; not a blueprint node).

Proof: on the slice U, regard the displayed matrix q as a presentation by
constant free k-module sheaves. Inverse scalar restriction along c and section reconstruction
identify its entries with sections of the discrete coefficient ring pulled back from A.
The constant-sheaf pullback comparison and e identify this ring with the constant ring
ULift A. Refine the slice covering until every entry of this finite matrix is a constant
ULift A scalar, using local surjectivity of the sheafification unit and finite intersections
of covering sieves. On each refined member form the cokernel P of the same finite matrix
between regular discrete point modules; this is a real cokernel, finitely presented by
construction, with the same ranks m and n as q. Pullback, section reconstruction and slice
restriction preserve the finite free presentation and its cokernel. Their inverse-image
comparison therefore identifies this point cokernel with the given restriction of N.
Full faithfulness of the section and
small-site equivalences reflects the resulting cokernel isomorphism. Empty matrices and
empty schemes use the same construction. No Noetherianity is needed, since the finite
presentation is displayed. The refinement accommodates any coefficient isomorphism c. -/
theorem discrete_constant_presentation_lifting
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type u) [CommRing A] (k : Type (u + 1)) [CommRing k]
    (e : ULift.{u + 1} A ≃+* k)
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (m n : ℕ)
    (q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k))
    (hN : Nonempty (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((coefficientModelFixedScalars _ k).obj
            ((smallModules X (condensedRingObj (discreteObj A) X) ⋙
              ConstantCompletion.res c.hom).obj N))).over U ≅
      (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k)).obj (cokernel q))) :
    ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
      ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
        ∃ d : pointModelFree (discreteObj A) m ⟶ pointModelFree (discreteObj A) n,
          Nonempty
            (pointModelRestriction (discreteObj A) f N (AsSmall.down.obj V).hom ≅
              (pointModelPullbackFunctor (discreteObj A) (AsSmall.down.obj V).left).obj
                (cokernel d)) := by
  let _ := e
  obtain ⟨a, ha⟩ := constant_slice_internal_presentation f (discreteObj A) k c N U m n q hN
  exact presentation_of_local_matrix (discreteObj A) f N U m n a ha
    (discrete_internal_matrix_local_lifting A U m n a)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
