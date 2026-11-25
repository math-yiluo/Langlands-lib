/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatibleIntegralRootBases
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Local bases of the integral Tate module

## References

* Bhatt–Scholze, The pro-étale topology for schemes, Section 6.8
* Bhatt–Scholze, Section 6.8
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem weaklyEtale_preservesLimits {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    PreservesLimitsOfShape ℕᵒᵖ ((upperStar Ab.{u + 1} f).mapMod R) := by
  let F := upperStar Ab.{u + 1} f
  have : PreservesLimitsOfShape ℕᵒᵖ (localizationRestriction Ab.{u + 1} f
      (inferInstance : WeaklyEtale f)) := by
    unfold localizationRestriction
    infer_instance
  have : PreservesLimitsOfShape ℕᵒᵖ F :=
    preservesLimitsOfShape_of_natIso
      (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).symm
  have : PreservesLimitsOfShape ℕᵒᵖ (F.mapMod R ⋙ Mod.forget (F.obj R)) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (Mod.forget R ⋙ F))
  have : ReflectsLimitsOfShape ℕᵒᵖ (Mod.forget (F.obj R) :
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (F.obj R) ⥤ _) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (F.mapMod R) (Mod.forget (F.obj R))

/-- The integral Tate module has a pro-étale local basis. -/
theorem tateModule_locally_trivial
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(X, ⊤)))
    : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty
        (((upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)).obj
              (tateModule X ℓ) ≅ 𝟙_ _) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_tateModule_residue_diagram_iso X ℓ hℓ
  refine ⟨𝒰, fun i ↦ ?_⟩
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let F := upperStar Ab.{u + 1} (𝒰.f i)
  let : F.Braided := CondensedRing.braided_sheafUpperStar _
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have : PreservesLimitsOfShape ℕᵒᵖ (F.mapMod R) := weaklyEtale_preservesLimits (𝒰.f i) R
  obtain ⟨e⟩ := h𝒰 i
  obtain ⟨hc⟩ := tateResidueModuleCone_isLimit X ℓ
  exact ⟨preservesLimitIso (F.mapMod R) (tateModuleSystem X ℓ) ≪≫
    HasLimit.isoOfNatIso e ≪≫
    (preservesLimitIso (F.mapMod R) (tateResidueModuleSystem X ℓ)).symm ≪≫
    (F.mapMod R).mapIso
      (hc.conePointUniqueUpToIso
        (limit.isLimit (tateResidueModuleSystem X ℓ))).symm ≪≫
    F.mapModUnitIso.symm⟩

end AlgebraicGeometry.ProEtale
