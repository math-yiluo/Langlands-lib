/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit

/-!
# Étale cohomology of modules commutes with large filtered colimits

Let `Y` be a quasi-compact quasi-separated scheme and `Λ` a commutative ring. The derived functors
`RᵠΓ(Y, -)` of the global sections of étale sheaves of `Λ`-modules commute with filtered colimits
indexed by categories in `Type (u + 1)`
(`AlgebraicGeometry.Scheme.preservesColimitsOfShape_rightDerived_Γ_moduleCat`), such as the
category of finite free modules over a `Λ`-module. For abelian sheaves this is
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_small` ([Stacks 03Q6]); we transport it
along the identification of `Sheaf.H` with the derived functors of the global sections
(`AlgebraicGeometry.Scheme.nonempty_sheafH_extDerivedIso`) and along the forgetful functor from
`Λ`-modules to abelian groups (`AlgebraicGeometry.Scheme.nonempty_etaleModuleCohomology_forgetIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
  (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]

/-- On a quasi-compact quasi-separated scheme, the étale cohomology groups `Hᵠ(Y, -)` of abelian
sheaves commute with filtered colimits indexed by categories in `Type (u + 1)`. -/
lemma preservesColimitsOfShape_functorH (q : ℕ) :
    PreservesColimitsOfShape J (Sheaf.functorH.{u + 1} Y.smallEtaleTopology q) := by
  have : ReflectsColimitsOfShape J (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨fun {D} ↦ ⟨fun {c} hc ↦
    ⟨isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1}) ?_⟩⟩⟩
  obtain ⟨h₁, h₂⟩ := H_map_isColimit_of_isFiltered_small Y hc q
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun k x y h ↦ ?_)
  · obtain ⟨k, y, hy⟩ := h₁ x
    exact ⟨k, y, hy.symm⟩
  · obtain ⟨k', a, ha⟩ := h₂ k (x - y) (by
      change Sheaf.H.map (c.ι.app k) q x = Sheaf.H.map (c.ι.app k) q y at h
      rw [map_sub, h, sub_self])
    refine ⟨k', a, ?_⟩
    change Sheaf.H.map (D.map a) q x = Sheaf.H.map (D.map a) q y
    rwa [map_sub, sub_eq_zero] at ha

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The étale cohomology `Hᵠ(Y, F)` of a sheaf `F` of `Λ`-modules placed in degree `0` is the
`q`-th right derived functor of the global sections. -/
noncomputable def singleFunctorCompCohomologyIsoRightDerived (Y : Scheme.{u}) (q : ℕ) :
    DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ) ≅
      (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q :=
  Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
      (Functor.isoWhiskerRight (Sheaf.Γ Y.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlusCompatibility.symm
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ))) ≪≫
    (Sheaf.Γ Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q

/-- On a quasi-compact quasi-separated scheme, the derived functors `RᵠΓ(Y, -)` of the global
sections of étale sheaves of `Λ`-modules commute with filtered colimits indexed by categories in
`Type (u + 1)`. -/
lemma preservesColimitsOfShape_rightDerived_Γ_moduleCat (q : ℕ) :
    PreservesColimitsOfShape J
      ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let S := sheafCompose Y.smallEtaleTopology U
  have : S.IsLeftAdjoint := moduleSheafForgetIsLeftAdjoint Y Λ
  have : ReflectsColimitsOfShape J U := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have := preservesColimitsOfShape_functorH Y J q
  have : PreservesColimitsOfShape J
      (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)) :=
    preservesColimitsOfShape_of_natIso (nonempty_sheafH_extDerivedIso Y q).some
  have : PreservesColimitsOfShape J
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)) ⋙ U) :=
    preservesColimitsOfShape_of_natIso (nonempty_etaleModuleCohomology_forgetIso Y Λ q).some.symm
  have := preservesColimitsOfShape_of_reflects_of_preserves
    (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)) U (J := J)
  exact preservesColimitsOfShape_of_natIso (singleFunctorCompCohomologyIsoRightDerived Λ Y q)

end AlgebraicGeometry.Scheme
