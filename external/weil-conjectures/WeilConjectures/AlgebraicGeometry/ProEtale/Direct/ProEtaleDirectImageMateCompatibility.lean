/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# ProEtaleDirectImageMateCompatibility

## References

* Stacks Tags 09A6 and 0B65
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [EnoughInjectives D] [EnoughInjectives D']
  {l : C ⥤ D} {r : D ⥤ C} {p : C' ⥤ D'} {t : D' ⥤ C'}
  {a : C ⥤ C'} {b : D ⥤ D'}
  [l.Additive] [r.Additive] [p.Additive] [t.Additive] [a.Additive] [b.Additive]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]

private theorem derived_mate_eq (e : l ⊣ r) (d : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv e d σ.hom) =
      (mateEquiv e.derivedPlus d.derivedPlus θ.hom) := by
  dsimp only
  let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
  have hθ (N : HomotopyCategory.Plus C) :
      θ.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        D+(b).map (l.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        b.mapDerivedCategoryPlusFactorsh.hom.app (l.mapHomotopyCategoryPlus.obj N) =
      D+(p).map (a.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        p.mapDerivedCategoryPlusFactorsh.hom.app (a.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh l b N]
    rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N]
    rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh a p N]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Functor.rightDerived_ext (R+(r) ⋙ D+(a))
    (Functor.whiskerRight r.rightDerivedFunctorPlusUnith D+(a) ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso D)
  apply NatTrans.ext
  funext M
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (mateEquiv e d σ.hom)) M
  have hm := Adjunction.derivedPlus_mateEquiv_app_fac e d σ.hom θ.hom hθ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf ⊢
  rw [hf, hm]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

end

variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem underived_comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj K) ≫ t) h

private theorem underived_comparison_mate {U V : Scheme.{u}} (f : U ⟶ V) :
    lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ) =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom) := by
  apply NatTrans.ext
  funext K
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
    underived_comparison_counit Λ f K

end AlgebraicGeometry.ProEtale
