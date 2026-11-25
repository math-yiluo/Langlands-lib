/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion

/-! # Unbounded proper base change for finite cyclic coefficients -/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme
variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Proper base change on unbounded complexes with coefficients in Z/nZ, n positive.
Source: Stacks Project, Tag 0F0C (Lemma 59.92.3), with Tags 095U, 07K7, and 079P.
(blueprint: theorem-results-from-etale-theory--1)

Proof in words: use the existing acyclic-complex criterion for the canonical
unbounded exchange. Underived proper base change supplies its sheaf exchange
hypothesis. Bounded-below proper base change makes the inverse image of each
injective torsion module sheaf acyclic for the base-changed direct image.

For the remaining hypothesis, fix a geometric point of the target. Its fibre
is proper over an algebraically closed field, hence has some finite dimension d.
Bounded-below proper base change, exactness of inverse image, and the comparison
between classical right derived functors and homology of the derived image
identify the pullback of R^q f'_* M with the higher direct image on this fibre.
The torsion dimension bound makes this zero for q > 2d, uniformly in M.
The bound may depend on the point. Geometric-point pullbacks preserve monomorphisms
and jointly detect zero sheaves. Pointwise finite-dimension shifting therefore
shows that f'_* preserves exact complexes of f'_*-acyclic sheaves. The unbounded
exchange criterion now applies: on a K-injective representative with injective
terms, both comparison units and the termwise underived exchange are invertible,
and its mate factorization identifies their composite with the canonical exchange.

The coefficient ring is finite because n > 0; consequently it and every module
sheaf over it are additively torsion. This includes n = 1. There is no global
quasi-compactness, Noetherian, or invertibility assumption. The pointwise argument
adapts the existing source-library proof in BaseChangeTheorems.Proper, without
importing that module, which would create a cycle. -/
theorem Etale.isIso_derivedBaseChangeMap_of_isProper_modN
    (n : ℕ) (hn : 0 < n) [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) sq.toCommSq) := open scoped Etale in by
  classical
  let Λ := ULift.{u + 1} (ZMod n)
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have hzero {T : Scheme.{u}}
      (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (H : ∀ t : T, IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj M)) :
      IsZero M := by
    let z := isZero_zero (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    have : IsIso (z.from_ M) := by
      refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (fun t ↦ T.algClosurePoint t)
        (fun t ↦ ⟨t, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
        fun t ↦ ?_
      have hz := Functor.map_isZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ]) z
      exact ⟨⟨hz.to_ _, (H t).eq_of_src _ _, hz.eq_of_src _ _⟩⟩
    exact IsZero.of_iso z (asIso (z.from_ M))
  have hbound {S T : Scheme.{u}} (p : S ⟶ T) [IsProper p] (t : T) :
      ∃ d : ℕ, ∀ (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
        IsZero ((T.algClosurePoint t)^*[ModuleCat.{u + 1} Λ].obj
          ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G)) := by
    let x := T.algClosurePoint t
    let fibreSq := IsPullback.of_hasPullback p x
    have : IsProper (pullback.snd p x) := IsProper.pullback_snd p x
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (pullback.snd p x)
    refine ⟨2 * d, fun G q hq ↦ ?_⟩
    have hvan := Etale.isZero_higherDirectImage_of_two_mul_lt hΛ (pullback.snd p x)
      (pullback.snd p x) (𝟙 _) (Category.comp_id _) d hd
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst p x)).obj G) q (by omega)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    have hMG : Scheme.IsTorsionModuleSheaf G :=
      Scheme.IsTorsionModuleSheaf.of_isTorsion hΛ G
    have hF : Scheme.IsTorsionAbelianSheaf
        ((sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) :=
      (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
        ((Scheme.isTorsionModuleSheaf_iff_isTorsion G).1 hMG)
    let φ : ULift.{u + 1} ℤ →+* Λ :=
      (Int.castRingHom Λ).comp (ULift.ringEquiv.{0, u + 1}).toRingHom
    let R := Sheaf.restrictScalars S.smallEtaleTopology φ
    let Φ := sheafCompose S.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
    let F := (sheafCompose S.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
    let e : Φ.obj (R.obj G) ≅ F := Iso.refl _
    have hFa : Scheme.IsTorsionAbelianSheaf F := hF
    have hh := Etale.isIso_derivedBaseChangeMapPlus_torsion_assembly fibreSq F hFa
    let eK := (Φ.mapDerivedCategoryPlusSingleFunctor 0).app (R.obj G) ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e
    have hA := hh.1
    rw [← NatTrans.isIso_app_iff_of_iso _ eK] at hA
    let eR := (R.mapDerivedCategoryPlusSingleFunctor 0).app G
    let eRΦ := Φ.mapDerivedCategoryPlus.mapIso eR
    change IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      fibreSq.toCommSq).app (Φ.mapDerivedCategoryPlus.obj
        ((R ⋙ DerivedCategory.Plus.singleFunctor _ 0).obj G))) at hA
    rw [← NatTrans.isIso_app_iff_of_iso _ eRΦ] at hA
    have hR' : IsIso ((Etale.derivedBaseChangeMapPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) fibreSq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0 ⋙ R.mapDerivedCategoryPlus).obj G)) := by
      rw [← Etale.isIso_derivedBaseChangeMapPlus_app_forget₂_iff]
      exact hA
    have hbc : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        fibreSq.toCommSq).app K) := by
      rw [← Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff φ
        fibreSq.toCommSq K]
      exact hR'
    refine IsZero.of_iso hvan
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapIso
          ((p)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso
            G q).symm ≪≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlusHomologyFunctorIso
          q).app ((Etale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.obj K) ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
            fibreSq.toCommSq).app K)) ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ)
            (pullback.snd p x)).rightDerivedFunctorPlus.mapIso
            (((Etale.upperStar (ModuleCat.{u + 1} Λ)
              (pullback.fst p x)).mapDerivedCategoryPlusSingleFunctor 0).app G)))
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    Etale.isIso_baseChangeMap_of_isProper Λ sq
  refine Etale.isIso_derivedBaseChangeMap_of_isIso_baseChangeMap _ sq.toCommSq
    (fun M hM hM' ↦ ?_) (fun I _ ↦ ?_)
  · choose d hd using hbound f'
    exact hM.map_of_rightAcyclic_of_forall_isZero _
      (fun y ↦ Etale.upperStar (ModuleCat.{u + 1} Λ) (Y'.algClosurePoint y))
      hzero d hd hM'
  · have : IsTorsionModuleSheaf I := .of_isTorsion hΛ _
    exact (Etale.HasTorsionBaseChange.hasInjectiveAcyclicity Λ f
      (Etale.hasTorsionBaseChange_of_isProper Λ f)).rightAcyclic Λ sq I

end AlgebraicGeometry
