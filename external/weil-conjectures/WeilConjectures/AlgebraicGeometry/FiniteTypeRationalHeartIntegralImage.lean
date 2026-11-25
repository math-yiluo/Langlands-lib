/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralSingle
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Integral sheaf models for rational direct images

Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13, Proposition 6.8.14(2),
and Remark 6.8.15 (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include k

-- Retain all geometric hypotheses of the assigned interface.
set_option linter.unusedSectionVars false in
/-- A rational constructible sheaf has an ordinary integral model whose direct image
localizes to the rational direct image. No cohomological upper bound is asserted.
Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13, Proposition 6.8.14(2), Remark 6.8.15.
(auxiliary; not a blueprint node)

Proof. Choose the bounded constructible integral model of F[0]. Exactness of
localization identifies its zeroth cohomology N with an ordinary integral model
of F; N is constructible by the definition of bounded constructibility. Place N
in degree zero, obtaining a bounded constructible integral complex. The qcqs
localization/direct-image comparison is invertible on this complex. Compose it
with the derived image of the single-complex localization isomorphism. The
empty scheme and zero sheaf are included by these same constructions.
-/
theorem finiteTypeRationalHeart_integralImage
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X.left),
      IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X.left) N ∧
      Nonempty (
        ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y.left)).leftDerivedFunctor.obj
          ((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))) ≅
        ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiCompact f.left := inferInstance
  have : QuasiSeparated f.left := inferInstance
  obtain ⟨M, ⟨eM⟩⟩ := continuousConstructible_integral_single_model ℓ E X.left F hF
  let N := (DerivedCategory.homologyFunctor _ 0).obj M.obj
  have hN : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X.left) N :=
    M.property.2 0
  let eN : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X.left)).obj N ≅ F :=
    (Functor.leftDerivedFunctorHomologyFunctorIso
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X.left)) 0).app M.obj ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso eM ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F
  let K : integralConstructible ℓ E X.left :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj N, by
      rw [ProEtale.mem_boundedConstructible_iff]
      refine ⟨⟨0, 0, ?_⟩, ?_⟩
      · intro i hi
        rcases hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
      · intro i
        rcases eq_or_ne i 0 with rfl | hi
        · exact _root_.constructible_of_iso
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm hN
        · rcases lt_or_gt_of_ne hi with hi | hi
          · exact ProEtale.constructible_of_isZero _ _
              (DerivedCategory.isZero_of_isGE _ 0 i hi)
          · exact ProEtale.constructible_of_isZero _ _
              (DerivedCategory.isZero_of_isLE _ 0 i hi)⟩
  let eK : (integralScalarExtension ℓ E X.left).obj K.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj F :=
    (Functor.singleFunctorCompLeftDerivedFunctorIso
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X.left))).app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eN
  have : IsIso ((derivedPushHom (integralScalarMap ℓ E) f.left).app K.obj) :=
    integralScalarPushHom_isIso ℓ E f.left K
  exact ⟨N, hN, ⟨asIso ((derivedPushHom (integralScalarMap ℓ E) f.left).app K.obj) ≪≫
    (R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).mapIso eK⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
