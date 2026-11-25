/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import all WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift

/-!
# Acyclicity of the affine line over a base

For a scheme `S` and a coefficient ring `Λ`, `AlgebraicGeometry.Etale.AffineLineAcyclicAt Λ S`
says that the unit `K ⟶ Rπ_* π^* K` of the derived adjunction `π^* ⊣ Rπ_*` on bounded below
derived categories of étale sheaves of `Λ`-modules is an isomorphism for every `K`, where
`π : 𝔸¹_S ⟶ S` is the projection of the affine line (SGA 4 XV 2.2; Fu, *Étale cohomology
theory*, 7.7).

## Main statements

- `AlgebraicGeometry.Etale.affineLineAcyclicAt_iff_singleFunctor`: it suffices to check the unit
  at sheaves placed in degree `0`.
- `AlgebraicGeometry.Etale.isIso_unit_app_singleFunctor_iff`: at a sheaf `F` placed in degree
  `0` the unit is an isomorphism if and only if it is an isomorphism `F ≅ H⁰(Rπ_* π^* F)` in
  degree `0` and the higher direct images `Rᵠπ_* π^* F`, `q > 0`, vanish.
- `AlgebraicGeometry.Etale.AffineLineAcyclicAt.of_surjective`: the property descends along a
  surjective `g : S' ⟶ S` along which the derived base change map of `π` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

/-- The unit form of a mate: if `β` is the mate of `α : G ⋙ L₂ ⟶ L₁ ⋙ H` with respect to the
adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, then `G(η₁) ≫ β = η₂ ≫ R₂(α)`. -/
lemma CategoryTheory.unit_comp_app_of_eq_mateEquiv {C D C' D' : Type*} [Category* C]
    [Category* D] [Category* C'] [Category* D'] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'}
    {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (G : C ⥤ C') (H : D ⥤ D')
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hβ : ∀ K, β.app K = (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)).app K)
    (c : C) :
    G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c) = adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) := by
  rw [hβ]
  exact unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) c

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The unit of the bounded below derived adjunction `f^* ⊣ Rf_*` commutes with the shifts. -/
instance commShift_derivedUpperStarLowerStarAdjunctionPlus_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    NatTrans.CommShift (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit
      ℤ := by
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  exact derivedUnit_commShift _

/-- **Acyclicity of the affine line over `S`**: for every bounded below complex `K` of étale
sheaves of `Λ`-modules on `S`, the unit `K ⟶ Rπ_* π^* K` of the projection
`π : 𝔸¹_S ⟶ S` is an isomorphism. -/
def AffineLineAcyclicAt (S : Scheme.{u}) : Prop :=
  ∀ K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app K)

/-- The functor `π^* ⋙ Rπ_*` does not lower the cohomological degree. -/
lemma isZero_homologyFunctor_upperStar_lowerStar_obj {X S : Scheme.{u}} (π : X ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((D+((π)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((π)_*[ModuleCat.{u + 1} Λ])).obj K)) :=
  isZero_homologyFunctor_baseChangeTarget_obj Λ π π K n q hq

/-- The unit of `π^* ⊣ Rπ_*` is an isomorphism at every bounded below complex as soon as it is an
isomorphism at every sheaf placed in degree `0`. -/
theorem isIso_unit_app_of_singleFunctor {X S : Scheme.{u}} (π : X ⟶ S)
    (h : ∀ F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app K) :=
  DerivedCategory.Plus.isIso_app_of_forall_homology _ ⊤ (fun F _ ↦ h F)
    (fun K n _ q hq ↦ DerivedCategory.Plus.isZero_homology_of_isGE K n q hq)
    (fun K n _ q hq ↦ isZero_homologyFunctor_upperStar_lowerStar_obj Λ π K n q hq) K
    (fun _ ↦ trivial)

/-- Acyclicity of the affine line can be checked on sheaves placed in degree `0`. -/
theorem affineLineAcyclicAt_iff_singleFunctor (S : Scheme.{u}) :
    AffineLineAcyclicAt Λ S ↔ ∀ F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  ⟨fun h _ ↦ h _, isIso_unit_app_of_singleFunctor Λ _⟩

/-- At a sheaf `F` placed in degree `0`, the unit `F ⟶ Rπ_* π^* F` is an isomorphism if and only
if it is an isomorphism on `H⁰` and the higher direct images `Rᵠπ_*(π^* F)`, `q > 0`, vanish. -/
theorem isIso_unit_app_singleFunctor_iff {X S : Scheme.{u}} (π : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ∧
      ∀ q : ℤ, 0 < q → IsZero (higherDirectImage Λ π q ((π)^*[ModuleCat.{u + 1} Λ].obj F)) := by
  let e : (D+((π)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((π)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      R+((π)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((π)^*[ModuleCat.{u + 1} Λ].obj F)) :=
    R+((π)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F)
  have hT (q : ℤ) : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((D+((π)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((π)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ↔
      IsZero (higherDirectImage Λ π q ((π)^*[ModuleCat.{u + 1} Λ].obj F)) :=
    ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e).isZero_iff
  refine ⟨fun h ↦ ⟨inferInstance, fun q hq ↦ ?_⟩, fun ⟨h₀, h⟩ ↦ ?_⟩
  · rw [← hT]
    exact IsZero.of_iso (DerivedCategory.Plus.isZero_homology_of_isLE
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 q hq)
      (asIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))).symm
  · rw [DerivedCategory.Plus.isIso_iff]
    intro q
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · exact isIso_of_source_target_iso_zero _
        (DerivedCategory.Plus.isZero_homology_of_isGE
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 q hq).isoZero
        (isZero_homologyFunctor_upperStar_lowerStar_obj Λ π _ 0 q hq).isoZero
    · exact h₀
    · exact isIso_of_source_target_iso_zero _
        (DerivedCategory.Plus.isZero_homology_of_isLE
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 q hq).isoZero
        ((hT q).2 (h q hq)).isoZero

/-- The degree-`0` higher direct image `R⁰π_* G` is the direct image `π_* G`. -/
noncomputable def higherDirectImageZeroIso {X S : Scheme.{u}} (π : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImage Λ π 0 G ≅ (π)_*[ModuleCat.{u + 1} Λ].obj G :=
  (DerivedCategory.homologyFunctor _ 0).mapIso
      (((π)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≪≫
    ((π)_*[ModuleCat.{u + 1} Λ]).singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.app
      G

/-- If the unit `F ⟶ Rπ_* π^* F` is an isomorphism at a sheaf `F` placed in degree `0`, then
`F ≅ π_* π^* F`. -/
theorem nonempty_iso_lowerStar_upperStar_of_isIso_unit_app {X S : Scheme.{u}} (π : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    Nonempty (F ≅ (π)_*[ModuleCat.{u + 1} Λ].obj ((π)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  ⟨((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app F).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (asIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) π).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso (R+((π)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    higherDirectImageZeroIso Λ π _⟩

/-- **The unit form of the derived base change map.** For a commutative square
`g' ≫ f = f' ≫ g`, the pullback along `g` of the unit `K ⟶ Rf_* f^* K` followed by the base
change map at `f^* K` is the unit `g^* K ⟶ Rf'_* f'^* g^* K` followed by the pullback
comparison `f'^* g^* K ≅ g'^* f^* K`. -/
lemma map_unit_baseChange_app {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((g)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).unit.app K) ≫
      (baseChange (ModuleCat.{u + 1} Λ) sq).app (D+((f)^*[ModuleCat.{u + 1} Λ]).obj K) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f').unit.app
        (D+((g)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((f')_*[ModuleCat.{u + 1} Λ]).map
        ((pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app K) := by
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  exact unit_comp_app_of_eq_mateEquiv _ _ _ _ _ _
    (baseChange_app_eq_mateEquiv (ModuleCat.{u + 1} Λ) sq) K

/-- A morphism of `D⁺(S_ét, Λ)` is an isomorphism if its pullback along a surjective morphism
`g : S' ⟶ S` is: the pullback commutes with the cohomology sheaves, and the pullback of
sheaves along `g` is conservative. -/
theorem isIso_of_isIso_upperStar_map_of_surjective {S S' : Scheme.{u}} (g : S' ⟶ S)
    [Surjective g]
    {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : K ⟶ L)
    (h : IsIso (D+((g)^*[ModuleCat.{u + 1} Λ]).map φ)) : IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (ι := PUnit.{u + 1}) (fun _ ↦ g) (fun x ↦ ⟨⟨⟩, g.surjective x⟩) _ fun _ ↦ ?_
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      (D+((g)^*[ModuleCat.{u + 1} Λ]).map φ)) := inferInstance
  exact (NatIso.isIso_map_iff
    (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso n) φ).2 this

/-- **Descent of the acyclicity of the affine line** along a surjective `g : S' ⟶ S`: if the
derived base change map of the projection `π : 𝔸¹_S ⟶ S` along `g` is an isomorphism at every
`π^* K` and the affine line over `S'` is acyclic, so is the affine line over `S`. -/
theorem AffineLineAcyclicAt.of_surjective {S S' : Scheme.{u}} (g : S' ⟶ S) [Surjective g]
    (hBC : ∀ K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((baseChange (ModuleCat.{u + 1} Λ)
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
          (D+((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ]).obj K)))
    (h : AffineLineAcyclicAt Λ S') : AffineLineAcyclicAt Λ S := by
  intro K
  refine isIso_of_isIso_upperStar_map_of_surjective Λ g _ ?_
  have hu := map_unit_baseChange_app Λ
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq K
  have := h (D+((g)^*[ModuleCat.{u + 1} Λ]).obj K)
  have : IsIso (D+((g)^*[ModuleCat.{u + 1} Λ]).map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app K) ≫
      (baseChange (ModuleCat.{u + 1} Λ)
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
          (D+((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [hu]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((baseChange (ModuleCat.{u + 1} Λ)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app _)

end Etale

end AlgebraicGeometry
