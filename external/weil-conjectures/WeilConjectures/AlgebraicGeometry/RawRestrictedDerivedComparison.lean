/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import all WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonEvaluationIsIso

/-! # Raw evaluation for bounded-below derived coefficients -/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

namespace RawRestrictedComparison

/-- Shifted restricted sections agree with degree-`q` cohomology. -/
noncomputable def derivedShiftIso {S Y : Scheme.{u}} (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (U : S.Etale) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).obj
      ((sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).obj
        (K⟦q⟧)) ≅
    (cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom h) q).obj
      ((upperStar AddCommGrpCat.{u + 1}
        (Limits.pullback.snd U.hom h)).mapDerivedCategory.obj K.obj) :=
  let T := sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).mapIso
      ((T.commShiftIso q).app K) ≪≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso q 0 q
      (add_zero q)).app _

end RawRestrictedComparison

/-- Evaluation on the free represented sheaf for a bounded-below derived coefficient. -/
noncomputable def rawRestrictedDerivedComparison {S Y : Scheme.{u}} (h : Y ⟶ S)
    (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (U : S.Etale) :
    AddCommGrpCat.of ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        (RawRestrictedComparison.freeSheaf S U)) ⟶ K⟦q⟧) ⟶
    (cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom h) q).obj
      ((upperStar AddCommGrpCat.{u + 1}
        (Limits.pullback.snd U.hom h)).mapDerivedCategory.obj K.obj) := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{u + 1} h).obj (RawRestrictedComparison.freeSheaf S U)
  let x := (RawRestrictedComparison.zeroIso W A).inv (RawRestrictedComparison.generator h U)
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  exact RawRestrictedComparison.Evaluation.evaluate T x ≫
    (RawRestrictedComparison.derivedShiftIso h q K U).hom

/-- Evaluation is invertible for every bounded-below derived coefficient. -/
theorem isIso_rawRestrictedDerivedComparison {S Y : Scheme.{u}} (h : Y ⟶ S)
    (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (U : S.Etale) : IsIso (rawRestrictedDerivedComparison h q K U) := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{u + 1} h).obj (RawRestrictedComparison.freeSheaf S U)
  let x := (RawRestrictedComparison.zeroIso W A).inv (RawRestrictedComparison.generator h U)
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  have : IsIso (RawRestrictedComparison.Evaluation.evaluate T x (B := K⟦q⟧)) := by
    obtain ⟨n, hn⟩ := (K⟦q⟧).property
    have : (K⟦q⟧).IsGE n := ((K⟦q⟧).isGE_ι_obj_iff n).mp hn
    obtain ⟨J, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso (K⟦q⟧) n
    have := evaluation_isIso_on_injectives h U J
    exact evaluation_isIso_of_iso _ _ e
  unfold rawRestrictedDerivedComparison
  dsimp only
  infer_instance

end AlgebraicGeometry.Etale
