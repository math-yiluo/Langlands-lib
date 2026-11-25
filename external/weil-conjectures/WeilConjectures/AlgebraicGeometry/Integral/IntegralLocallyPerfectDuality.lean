/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectStratumPieces
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantPerfectModels
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentityInverseImageModules
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDuality
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Integral local models are perfect on the ringed site

## References

* Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.3.14(1)
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [-instance] CategoryTheory.flatConstantModulesAbelian
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

private def scalarRoundTrip {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  SheafOfModules.pushforwardComp (F := 𝟭 C) (G := 𝟭 C) c.inv c.hom ≪≫
    SheafOfModules.pushforwardCongr c.inv_hom_id ≪≫ SheafOfModules.pushforwardId S

private def scalarEquivalence {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (scalarRoundTrip c).symm
  counitIso := scalarRoundTrip c.symm
  functor_unitIso_comp M := by ext V x; rfl

private theorem identityLocalModel (X : Scheme.{u}) (R : Rings X) (U : X.ProEt)
    (K L : DerivedCategory (pbcModules X R))
    (h : Nonempty (integralLocalDerived (𝟙 X) R U K ≅
      integralLocalDerived (𝟙 X) R U L)) :
    Nonempty ((ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1}
      ((adicLisseForget X).obj R) U).obj K ≅
      (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1}
        ((adicLisseForget X).obj R) U).obj L) := by
  let R' := inverseRing (𝟙 X) R
  let S := (adicLisseForget X).obj R
  let S' := (adicLisseForget X).obj R'
  let c : S' ≅ S := (adicLisseForget X).mapIso (ringId R)
  let cU := ((ProEt.topology X).overPullback RingCat.{u + 1} U).mapIso c
  let E := scalarEquivalence cU
  have : E.functor.Additive := inferInstanceAs (SheafOfModules.restrictScalars _).Additive
  let F := SheafOfModules.overFunctor.{u + 1} S U
  let F' := SheafOfModules.overFunctor.{u + 1} S' U
  let : F.Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, u + 1} R U
  let : F'.Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, u + 1} R' U
  have : PreservesFiniteLimits F :=
    (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S U).1
  have : PreservesFiniteColimits F :=
    (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S U).2
  have : PreservesFiniteLimits F' :=
    (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S' U).1
  have : PreservesFiniteColimits F' :=
    (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S' U).2
  let H := proEtaleRingModulePullback (𝟙 X) R R' (Iso.refl _)
  obtain ⟨t⟩ := proEtaleRawIdentityPullback_comparison X R
  let s : H ⋙ F' ≅ F ⋙ E.functor :=
    Functor.isoWhiskerRight t F' ≪≫ (Iso.refl _)
  let ds : H.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ E.functor.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso H F' ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso F E.functor).symm
  let α (M : DerivedCategory (pbcModules X R)) :
      integralLocalDerived (𝟙 X) R U M ≅
        E.functor.mapDerivedCategory.obj (F.mapDerivedCategory.obj M) :=
    SheafOfModules.overFunctor_derivedRestrictionIso.{u + 1, u, u + 1}
      S' U (H.mapDerivedCategory.obj M) ≪≫
      ds.app M
  obtain ⟨e⟩ := h
  exact ⟨E.functor.mapDerivedCategory.preimageIso ((α K).symm ≪≫ e ≪≫ α L)⟩

/-- The completed constant local-model condition gives actual perfectness on the
ringed site with its independent coefficient universe. -/
theorem integralLocallyPerfect_sitePerfect
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (L : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (hL : IsIntegralLocallyPerfect X d L) :
    SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, u + 1}
      (pbcAdicCompletion X d) L := by
  classical
  let J := ProEt.topology X
  let R := pbcAdicCompletion X d
  let S := (adicLisseForget X).obj R
  let F (U : X.ProEt) :=
    ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1} S U
  have eF (U : X.ProEt) : DerivedCategory.Q ⋙ F U ≅
      (SheafOfModules.overFunctor.{u + 1} S U).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q := by
    let G := SheafOfModules.overFunctor.{u + 1} S U
    let : G.Additive :=
      SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, u + 1} R U
    let : PreservesFiniteLimits G :=
      (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S U).1
    let : PreservesFiniteColimits G :=
      (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S U).2
    exact G.mapDerivedCategoryFactors
  apply (perfect_local_models.{u + 1, u, u + 1} J R F eF L).mpr
  obtain ⟨V, hV, hm⟩ := hL.2
  intro B
  let f : B ⟶ ⊤_ X.ProEt := terminal.from B
  refine ⟨V.pullback f, J.pullback_stable f hV, ?_⟩
  intro U g hg
  obtain ⟨P, hP, he⟩ := hm U (g ≫ f) hg
  obtain ⟨e⟩ := identityLocalModel X R U L ((integralConstantDerived X d).obj P) he
  obtain ⟨E, ⟨a, b, hb⟩, ⟨p⟩, ⟨q⟩⟩ := integralConstantDerived_strictPerfectModel X d P hP
  let G := SheafOfModules.overFunctor.{u + 1} S U
  let : G.Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{u + 1, u, u + 1} R U
  have : PreservesFiniteLimits G :=
    (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S U).1
  have : PreservesFiniteColimits G :=
    (SheafOfModules.overFunctor_exact_ofUniverses.{u + 1, u, u + 1} S U).2
  refine ⟨(G.mapHomologicalComplex (.up ℤ)).obj E, ⟨a, b, ?_⟩,
    ⟨p.map G (Iso.refl _)⟩,
    ⟨e ≪≫ (F U).mapIso q ≪≫ G.mapDerivedCategoryFactors.app E⟩⟩
  intro n hn
  exact G.map_isZero (hb n hn)

end AlgebraicGeometry.Scheme
