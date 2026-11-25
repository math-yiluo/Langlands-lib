/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteNormalizedScalarRestriction
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteScalarRestrictionConstructible

/-! # Fixed-stratum local models under normalized finite scalar restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

private theorem ordinary_local_of_iso (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) {F G : Ordinary A T} (e : F ≅ G)
    (h : ordinaryFiniteLocalCondition A T F) : ordinaryFiniteLocalCondition A T G := by
  apply (Scheme.finiteLocal_iff T A G).mp
  exact isFiniteLocallyConstant_of_iso ((Scheme.proEtaleModuleRestriction T A).mapIso e)
    ((Scheme.finiteLocal_iff T A F).mpr h)

private theorem stratumCondition_iff (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    (X : Scheme.{u}) (S : Scheme.Stratification X) (i : Fin S.n)
    (eX : Encoding A X) (eT : Encoding A (S.domain i)) (M : Internal A X) :
    HasFiniteConstantLocalModel (coefficient A) (S.domain i)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) ↔
    ordinaryFiniteLocalCondition A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A
        (eX.ordinary.functor.obj M)) := by
  let N := (CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M
  let F := Scheme.proEtaleConstantModulePullback (S.immersion i) A
    (eX.ordinary.functor.obj M)
  let h := (fixedIso A (S.domain i) eT (eT.ordinary.functor.obj N)).symm ≪≫
    encodedPullbackIso A (S.immersion i) eX eT M
  refine (localCondition_iff A (S.domain i) eT N).trans ?_
  refine (Scheme.finiteLocal_iff (S.domain i) A _).symm.trans ?_
  exact (Iff.intro (isFiniteLocallyConstant_of_iso h)
    (isFiniteLocallyConstant_of_iso h.symm)).trans (Scheme.finiteLocal_iff _ A F)

private theorem ordinary_stratum_restriction
    (X : Scheme.{u}) [IsNoetherian X]
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B] (a : A →+* B)
    (F : Ordinary B X) (S : Scheme.Stratification X) (i : Fin S.n)
    (hS : ordinaryFiniteLocalCondition B (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) B F)) :
    ordinaryFiniteLocalCondition A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A
        ((Scheme.proEtaleRingRestrictScalars
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj F)) := by
  classical
  obtain ⟨I, U, f, hc, ht⟩ := hS.1
  choose M hM using ht
  have htr := Scheme.proEtaleFiniteScalarRestriction_sameTrivializations
    X A B a F S i I U f hc M hM
  refine ⟨⟨I, U, f, hc, fun j ↦ ⟨_, htr j⟩⟩, ?_⟩
  intro Ω _ _ y
  let e := (Scheme.geometricRingModuleStalkFunctor y
    (Scheme.proEtaleConstantRing (S.domain i) A)).mapIso
      (Scheme.pullbackRestrictionIso (S.immersion i) A B a F)
  have : Finite (Scheme.proEtaleGeometricModuleStalk y
      (Scheme.proEtaleConstantRing (S.domain i) B)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) B F)) := hS.2 Ω y
  have : Finite ((Scheme.geometricRingModuleStalkFunctor y
      (Scheme.proEtaleConstantRing (S.domain i) A)).obj
      ((Scheme.proEtaleRingRestrictScalars
        ((constantSheaf (Scheme.ProEt.topology (S.domain i)) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom a.ulift.{u + 1, u + 1}))).obj
        (Scheme.proEtaleConstantModulePullback (S.immersion i) B F))) := ‹_›
  exact Finite.of_injective e.toLinearEquiv e.toLinearEquiv.injective

/-- Normalized restriction of finite coefficients preserves finite constant local
models on each specified stratum, without changing that stratum.
Source: integral-finite-levels, first paragraph, and integral-criterion reductions,
finite scalar restriction step. (blueprint: lem-pe-finite-scalar-local-transport).

Proof: compare finite constant models to ordinary locally constant sheaves with finite
stalks. Ordinary restriction preserves their chosen local trivializations and the
underlying geometric stalk sets on the specified stratum. The normalized coefficient
square identifies this restriction with internal restriction. Exactness identifies the
restricted homology with homology after restriction. Apply the sheaf comparison in every
degree and transport the models across these isomorphisms. -/
theorem finite_scalar_local_transport
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [Finite A] [Finite B] [DiscreteTopology A] [DiscreteTopology B]
    (a : A →+* B) (ρ : coefficient A ⟶ coefficient B) [IsMonHom ρ]
    (hρ : pointConstants A ≫ ρ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫ pointConstants B)
    (X : Scheme.{u}) [IsNoetherian X] (S : Scheme.Stratification X) (i : Fin S.n)
    (K : DerivedCategory (Internal B X))
    (hK : ∀ q : ℤ, HasFiniteConstantLocalModel (coefficient B) (S.domain i)
      ((CondensedRing.upperStar (coefficient B) (S.immersion i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj K))) :
    ∀ q : ℤ, HasFiniteConstantLocalModel (coefficient A) (S.domain i)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Mod.comap ((upperStarFromPoint X).map ρ)).mapDerivedCategory.obj K))) := by
  let eA := (encoding_exists A X).some
  let eB := (encoding_exists B X).some
  let eAT := (encoding_exists A (S.domain i)).some
  let eBT := (encoding_exists B (S.domain i)).some
  obtain ⟨e⟩ := finite_normalized_scalar_restriction A B a ρ hρ X eA eB
  let R : Internal B X ⥤ Internal A X :=
    Mod.comap ((upperStarFromPoint X).map ρ)
  intro q
  apply (stratumCondition_iff A X S i eA eAT _).mpr
  have hB := (stratumCondition_iff B X S i eB eBT _).mp (hK q)
  have hR := ordinary_stratum_restriction X A B a _ S i hB
  let eh := eA.ordinary.functor.mapIso
    ((R.mapDerivedCategoryHomologyFunctorIso q).app K).symm ≪≫
      e.app ((DerivedCategory.homologyFunctor _ q).obj K)
  have := Scheme.constantComparison_isIso (S.immersion i) A
  let P := Scheme.proEtaleRingModulePullback (S.immersion i)
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing (S.domain i) A)
    (asIso (Scheme.proEtaleCoefficientInverseImageMap (S.immersion i) A))
  exact ordinary_local_of_iso A (S.domain i) (P.mapIso eh).symm hR

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
