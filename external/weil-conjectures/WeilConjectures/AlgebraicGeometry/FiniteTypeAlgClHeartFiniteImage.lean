/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationDescent
import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison

/-! # Finite coefficient models for algebraic-closure direct images -/

@[expose] public section

set_option autoImplicit false
set_option maxSynthPendingDepth 0

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.leftDerivedFunctorIsoMapDerivedCategory
  Mod.monoidalCategory Mod.monoidalCategoryStruct Mod.monoidalClosed
  upperStarFromPoint derivedPushHom derivedComapLowerStarIso

attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
  Mod.hasFunctorialFlatResolution sheafMonoidalCategory sheafMonoidalClosed
  hasFunctorialFlatResolution_sheaf

-- Cache the tensor instances before specializing the coefficient ring. Otherwise
-- elaborating the theorem's derived scalar functor expands the graded tensor construction.
section TensorInstances

variable (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

private instance cachedModulePreadditive :
    MonoidalPreadditive (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedGood12
    (P Q S : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q S := by
  infer_instance

private instance cachedGood23
    (P Q S : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q S := by
  infer_instance

private instance cachedFour
    (P Q S V : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt P Q S V := by
  infer_instance

private instance cachedModuleFlatResolution :
    Abelian.HasFunctorialFlatResolution (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedExactSequential :
    HasExactColimitsOfShape ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

private instance cachedTensorLeftSequential
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).obj M) := by
  infer_instance

private instance cachedTensorRightSequential
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).flip.obj M) := by
  infer_instance

end TensorInstances

attribute [local instance 20000] cachedGood12 cachedGood23 cachedFour
  cachedTensorLeftSequential cachedTensorRightSequential

attribute [local instance 20000]
  PreservesColimitsOfShape.preservesColimit
  PreservesColimitsOfSize.preservesColimitsOfShape

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include ℓ k

set_option linter.unusedSectionVars false in
/-- The direct image of an algebraic-closure sheaf comes from a finite coefficient field.

Source: Bhatt--Scholze, Proposition 6.8.4(3), Proposition 6.8.14,
Remark 6.8.15 and bounded-below continuity in Section 6.3.
(auxiliary; not a blueprint node)

Proof: choose the finite constructible stratification of F. Finite-rank local systems,
their finite presentation matrices and their gluing data descend to a finite
subextension of the algebraic closure, by 6.8.4(3). Enlarge that subextension finitely
many times so that all strata and extension classes are defined over one E. This
constructs a constructible E-sheaf N whose scalar extension is F. Extension to the
algebraic closure is exact. It is the filtered colimit of the finite scalar extensions,
and on a qcqs map bounded-below direct image commutes with this filtered colimit.
Finite scalar extension commutes with direct image by a finite basis. Combining
these comparisons for N[0] gives the displayed isomorphism to Rf_*(F[0]). This is
only a scalar-change description, with no upper bound asserted for the image.
For the zero sheaf or empty source choose the base coefficient field and N=0. -/
theorem finiteTypeAlgClHeart_finiteImage
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) F) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (N : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (padicSubfieldRingObj X.left ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj X.left ℓ E) N ∧
      Nonempty (
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y.left ℓ E)).leftDerivedFunctor.obj
          ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj N)) ≅
        ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsNoetherian X.left := {}
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  obtain ⟨E, N, hN, ⟨e⟩⟩ := exists_constructible_finiteCoefficient_model X.left ℓ F hF
  refine ⟨E, N, hN, ?_⟩
  let K := (DerivedCategory.singleFunctor _ 0).obj N
  let C : DerivedCategory.Plus _ := ⟨K, ⟨0, inferInstance⟩⟩
  have : IsIso ((derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left).app K) :=
    isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E f.left C
  let T := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X.left ℓ E)
  have es₁ := T.singleFunctorCompLeftDerivedFunctorIso.app N
  dsimp only [Functor.comp_obj] at es₁
  have es₂ := (DerivedCategory.singleFunctor _ 0).mapIso e
  let es : T.leftDerivedFunctor.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F :=
    es₁ ≪≫ es₂
  exact ⟨asIso ((derivedPushHom
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left).app K) ≪≫
    (R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso es⟩

end AlgebraicGeometry.ProEtale.CondensedRing
