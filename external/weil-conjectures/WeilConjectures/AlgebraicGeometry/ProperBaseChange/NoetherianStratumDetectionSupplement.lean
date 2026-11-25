/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection

/-!
# Detection by pro-etale covers of finitely many locally closed strata

## References

* Stacks Project, Tags 09AH and 09AB, followed by finite-stratum induction
* Stacks, Tags 09AH and 09AB, and finite-stratum induction
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def modelSheafEquivalence (X : Scheme.{u})
    (D : Type*) [Category.{u + 1} D] :
    Sheaf (proEtaleModelTopology X) D ≌ Sheaf (ProEt.topology X) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      D (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      D (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

@[irreducible] private noncomputable def modelAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type*) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    (modelSheafEquivalence Y D).functor ⋙ proEtaleSheafInverseImage f D ⋙
      (modelSheafEquivalence X D).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous D
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f D).restrictFullyFaithful
    (modelSheafEquivalence Y D).fullyFaithfulFunctor
    (modelSheafEquivalence X D).fullyFaithfulFunctor (Iso.refl _) (Iso.refl _)

private theorem modelRingAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (modelAdjunction f RingCat.{u + 1}).unit.app
        ((modelSheafEquivalence Y RingCat.{u + 1}).inverse.obj R) =
      proEtaleRingModelUnit f R := by
  apply (modelSheafEquivalence Y RingCat.{u + 1}).functor.map_injective
  rw [modelAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl

private noncomputable def modelAbelianPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
        AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X) ⋙
      (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor ≅
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let a := modelAdjunction f AddCommGrpCat.{u + 1}
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)
  exact Functor.isoWhiskerLeft (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse
    (Functor.isoWhiskerRight (b.leftAdjointUniq a)
      (modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor)

/-- Abelian sheaves are detected by the chosen pro-etale covers of all strata. -/
theorem proEtale_isZero_of_stratum_cover (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : Stratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain a))
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (hF : ∀ (a : Fin S.n) (j : (V a).I₀),
      IsZero ((proEtaleSheafInverseImage ((V a).f j ≫ S.immersion a)
        AddCommGrpCat.{u + 1}).obj F)) : IsZero F := by
  -- Finite quasi-compact joint detection applies directly to the actual immersions.
  have : IsNoetherian X := {}
  have hstr (a : Fin S.n) :
      IsZero ((proEtaleSheafInverseImage (S.immersion a) AddCommGrpCat.{u + 1}).obj F) := by
    let G := (proEtaleSheafInverseImage (S.immersion a) AddCommGrpCat.{u + 1}).obj F
    let := HasZeroObject.zero'
      (Sheaf (ProEt.topology (S.domain a)) AddCommGrpCat.{u + 1})
    let : ∀ j, WeaklyEtale ((V a).f j) :=
      (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (V a).mem₀.2 |>.2
    have hz (j : (V a).I₀) :
        IsZero ((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          ((V a).f j)).obj G) :=
      (hF a j).of_iso ((AlgebraicGeometry.ProEtale.upperStarComp
        AddCommGrpCat.{u + 1} ((V a).f j) (S.immersion a)).symm.app F)
    have : IsIso (0 : G ⟶ 0) := by
      refine AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction
        AddCommGrpCat.{u + 1} (0 : G ⟶ 0) (V a).f (V a).mem₀ fun j ↦ ?_
      let e := AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
        AddCommGrpCat.{u + 1} ((V a).f j) inferInstance
      exact isIso_of_source_target_iso_zero _ ((hz j).of_iso (e.app G).symm).isoZero
        (((AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          ((V a).f j)).map_isZero (isZero_zero _)).of_iso (e.app 0).symm).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))
  have : ∀ a : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain a) := fun a ↦
    (S.immersion a).isEmbedding.noetherianSpace
  have : ∀ a : Fin S.n, QuasiCompact (S.immersion a) := fun a ↦ inferInstance
  rw [IsZero.iff_id_eq_zero]
  apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
  · intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · intro a
    rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
      (S.immersion a)).map_id]
    exact (hstr a).eq_of_src _ _

end AlgebraicGeometry.Scheme
