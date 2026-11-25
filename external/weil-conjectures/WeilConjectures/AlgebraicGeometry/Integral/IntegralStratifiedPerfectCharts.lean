/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange

/-!
# Stratified perfect models on covering schemes

The stratified-perfect condition gives perfect constant models on the slices of a
covering sieve of each stratum. Choosing a covering family generating the sieve turns
them into perfect constant models after inverse image to the covering schemes.

## References

* Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8
* Stacks Tags 0997 and 0998
* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

private def terminalIdentity (X : Scheme.{u}) : IsTerminal (ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _) (by trivial)) (by
      intro U f
      apply MorphismProperty.Over.Hom.ext
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 X = U.hom at hw
      exact (Category.comp_id _).symm.trans hw)

/-- Isomorphic slice restrictions over a weakly etale object give isomorphic inverse
images to the underlying scheme of that object, composed with the given morphism. -/
theorem nonempty_adicTowerPullback_comp_iso_of_local {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    {K L : DerivedCategory (pbcModules T R)}
    (e : Nonempty (integralLocalDerived g R U K ≅ integralLocalDerived g R U L)) :
    Nonempty ((adicTowerPullback (U.hom ≫ g) R).obj K ≅
      (adicTowerPullback (U.hom ≫ g) R).obj L) := by
  obtain ⟨e⟩ := e
  let Rg := (adicTowerInverseImage g).obj R
  obtain ⟨q, ⟨eq⟩⟩ := chartDerivedEquivalence U Rg
  let a : (adicTowerPullback U.hom Rg).obj ((adicTowerPullback g R).obj K) ≅
      (adicTowerPullback U.hom Rg).obj ((adicTowerPullback g R).obj L) :=
    q.fullyFaithfulFunctor.preimageIso
      (eq.app ((adicTowerPullback g R).obj K) ≪≫
        localRestrictionComparison g R U K ≪≫ e ≪≫
          (localRestrictionComparison g R U L).symm ≪≫
            (eq.app ((adicTowerPullback g R).obj L)).symm)
  let c := proEtaleRingCompositeCoefficients U.hom g R Rg
    ((adicTowerInverseImage U.hom).obj Rg) (Iso.refl _) (Iso.refl _)
  let P := proEtaleCanonicalDerivedPullbackComparison U.hom g R Rg
    ((adicTowerInverseImage U.hom).obj Rg) (Iso.refl _) (Iso.refl _)
  let s := derivedPullbackScalarIso (U.hom ≫ g) R _ c
  exact ⟨(s.app K).symm ≪≫ (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology U.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).mapDerivedCategory.mapIso
      (P.app K ≪≫ a ≪≫ (P.app L).symm) ≪≫ s.app L⟩

/-- A stratified-perfect complex has perfect constant models after inverse image to the
members of a pro-etale cover of each stratum. -/
theorem IsIntegralStratifiedPerfect.exists_cover_charts (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (hK : IsIntegralStratifiedPerfect T d K) :
    ∃ (S : Stratification T)
      (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a)),
      ∀ (a : Fin S.n) (j : (V a).I₀),
        ∃ C : completedConstantDerived (ModuleCat.{u + 1} A),
          @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C ∧
          Nonempty ((adicTowerPullback ((V a).f j ≫ S.immersion a)
              (pbcAdicCompletion T d)).obj K ≅
            (adicTowerPullback ((V a).f j ≫ S.immersion a) (pbcAdicCompletion T d)).obj
              ((integralConstantDerived T d).obj C)) := by
  classical
  obtain ⟨s, hs⟩ := hK
  choose W hW hw using hs
  let e (i : Fin s.n) : ProEt.mk (𝟙 (s.domain i)) ≅ ⊤_ (s.domain i).ProEt :=
    (terminalIdentity _).uniqueUpToIso terminalIsTerminal
  have covers (i : Fin s.n) : ∃ R : Presieve (ProEt.mk (𝟙 (s.domain i))),
      R ∈ ProEt.precoverage (s.domain i) _ ∧ R ≤ (W i).pullback (e i).hom := by
    have : (ProEt.precoverage (s.domain i)).IsStableUnderComposition := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).IsStableUnderBaseChange := by
      dsimp [ProEt.precoverage]; infer_instance
    have : (ProEt.precoverage (s.domain i)).HasIsos := by
      dsimp [ProEt.precoverage]; infer_instance
    exact (ProEt.precoverage (s.domain i)).mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      ((ProEt.topology (s.domain i)).pullback_stable (e i).hom (hW i))
  choose R hR hRW using covers
  let H (i : Fin s.n) := (R i).preZeroHypercover
  let F (i : Fin s.n) := ProEt.forget (s.domain i) ⋙ Over.forget (s.domain i)
  let V (i : Fin s.n) : Scheme.Cover.{u + 1} proetalePrecoverage (s.domain i) :=
    { toPreZeroHypercover := (H i).map (F i)
      mem₀ := by
        rw [PreZeroHypercover.presieve₀_map, Presieve.presieve₀_preZeroHypercover]
        exact hR i }
  refine ⟨s, V, fun i j ↦ ?_⟩
  obtain ⟨P, hP, he⟩ := hw i ((H i).X j) ((H i).f j ≫ (e i).hom) (hRW i _ _ j.2)
  have hf : (V i).f j = ((H i).X j).hom := by
    have hh := MorphismProperty.Over.w ((H i).f j)
    change ((H i).f j).left ≫ 𝟙 (s.domain i) = ((H i).X j).hom at hh
    change ((H i).f j).left = ((H i).X j).hom
    exact (Category.comp_id ((H i).f j).left).symm.trans hh
  refine ⟨P, hP, ?_⟩
  rw [hf]
  exact nonempty_adicTowerPullback_comp_iso_of_local (s.immersion i) _ ((H i).X j) he

end AlgebraicGeometry.Scheme
