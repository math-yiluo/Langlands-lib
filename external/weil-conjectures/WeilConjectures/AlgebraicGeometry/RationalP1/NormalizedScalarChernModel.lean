/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares

/-! # Scalar Chern transport through canonically normalized derived models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.RationalP1

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.leftDerivedUpperStarComp condensedAmbientPullbackComparison
  Adjunction.pullIsoOfComapIso Adjunction.pushHomOfComapIso

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward Mod.regular

-- Compare the full universal-unit normalizations before cancelling the derived models.
private theorem normalized_restriction_square
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (e : R.R = (CondensedRing.lowerStar Λ f).rightDerivedFunctor)
    (e' : R'.R = (CondensedRing.lowerStar Λ' f).rightDerivedFunctor)
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) R e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar Λ' f) R' e')
    (s : RestrictionSquare a f R R') :
    s.iso.hom ≫ Functor.whiskerLeft
        (Mod.comap (coefficientMap a X)).mapDerivedCategory (eqToIso e).hom =
      Functor.whiskerRight (eqToIso e').hom
        (Mod.comap (coefficientMap a S)).mapDerivedCategory ≫
        (derivedComapLowerStarIso a f).hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := Modules Λ' X))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨K, hK, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  change s.iso.hom.app (DerivedCategory.Q.obj K) ≫
      (eqToIso e).hom.app
        ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
    (Mod.comap (coefficientMap a S)).mapDerivedCategory.map
      ((eqToIso e').hom.app (DerivedCategory.Q.obj K)) ≫
      (derivedComapLowerStarIso a f).hom.app (DerivedCategory.Q.obj K)
  have := R'.computation K hK
  apply (cancel_epi ((Mod.comap (coefficientMap a S)).mapDerivedCategory.map
    (R'.η.app K))).1
  apply (cancel_mono ((CondensedRing.lowerStar Λ f).rightDerivedFunctor.map
    ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactors.hom.app K))).1
  simp only [Category.assoc]
  have hn := (eqToIso e).hom.naturality
    ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_obj] at hn
  rw [← hn, reassoc_of% (s.normalization K)]
  erw [he]
  erw [← Functor.map_comp_assoc, he']
  simpa only [derivedComapLowerStarIso, derived_square] using
    (canonicalSquare_normalization (CondensedRing.lowerStar Λ' f) (CondensedRing.lowerStar Λ f)
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a S))
    (comapLowerStarIso a f) K).symm

private theorem pushHom_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : C ⥤ D} {U' : D ⥤ C} (adj' : L' ⊣ U')
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (e : G = G') (e' : H = H')
    (s : H ⋙ U' ≅ U ⋙ G) (t : H' ⋙ U' ≅ U ⋙ G')
    (h : s.hom ≫ Functor.whiskerLeft U (eqToIso e).hom =
      Functor.whiskerRight (eqToIso e').hom U' ≫ t.hom) (K : A) :
    L'.map ((eqToIso e).hom.app K) ≫ (Adjunction.pushHomOfComapIso adj adj' t).app K =
      (Adjunction.pushHomOfComapIso adj adj' s).app K ≫ (eqToIso e').hom.app (L.obj K) := by
  subst G'
  subst H'
  have hs : s = t := by
    apply Iso.ext
    ext X
    have hx := congr_app h X
    simpa using hx
  subst t
  simp

private theorem normalized_push
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (e : R.R = (CondensedRing.lowerStar Λ f).rightDerivedFunctor)
    (e' : R'.R = (CondensedRing.lowerStar Λ' f).rightDerivedFunctor)
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) R e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar Λ' f) R' e')
    (s : RestrictionSquare a f R R') (K : DerivedCategory (Modules Λ X)) :
    (derivedScalars a S).map ((eqToIso e).hom.app K) ≫ (derivedPushHom a f).app K =
      (s.mate a).app K ≫ (eqToIso e').hom.app ((derivedScalars a X).obj K) := by
  unfold derivedPushHom RestrictionSquare.mate
  exact pushHom_transport _ _ e e' s.iso (derivedComapLowerStarIso a f)
    (normalized_restriction_square a f R R' e e' he he' s) K

/-- The explicit scalar Chern construction agrees with the canonical scalar push map. -/
theorem extendScalarChern_canonical
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (cU : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (cL : Endpoint a M M' m)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (e : R.R = (CondensedRing.lowerStar Λ f).rightDerivedFunctor)
    (e' : R'.R = (CondensedRing.lowerStar Λ' f).rightDerivedFunctor)
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) R e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar Λ' f) R' e')
    (s : RestrictionSquare a f R R')
    (x : unit Λ S ⟶ R.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧)) :
    extendScalarChern a f cU cL R R' s x ≫ (eqToIso e').hom.app _ =
      cU.iso.inv ≫ (derivedScalars a S).map (x ≫ (eqToIso e).hom.app _) ≫
        (derivedPushHom a f).app _ ≫
        (moduleObjectDerivedPushforward Λ' f).map (cL.shift a) := by
  unfold extendScalarChern
  simp only [Functor.map_comp, Category.assoc]
  rw [(eqToIso e').hom.naturality (cL.shift a)]
  rw [← reassoc_of% (normalized_push a f R R' e e' he he' s _)]

end AlgebraicGeometry.ProEtale.RationalP1
