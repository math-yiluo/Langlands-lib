/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Lower-degree comparison for open injective coefficients

Source: Stacks Project, Tag 0F07, condition (3).
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Functor
open scoped CategoryTheory.Functor

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The pulled-back coefficient counit is the lower-degree base-change comparison.
Source: Stacks Project, Tag 0F07, proof of condition (3), and Tag 0734.
(blueprint: lem-sbc-open-injective-coefficient-lower-comparison).

Proof: Resolve the injective coefficient J by J[0]. Thus Rj_* J[0] is canonically
(j_* J)[0]. The mate defining derived base change for the Cartesian square is the
unit of Da^* adjoint to Ra_*, followed by Ra_* of the pullback-square comparison
and the derived counit for j. On the injective single complex that counit is the
single of the ordinary counit, after the exact pullback single-complex comparison.
Consequently the displayed map agrees with base change, preceded by the canonical
isomorphism De^*((j_* J)[0]) → De^*Rj_*J[0]. Its degree-n homology is an
isomorphism by BaseChangeProperty for e in degree n. The proof holds also for
negative n, for the zero coefficient, and for the empty open immersion.
-/
theorem open_injective_coefficient_lower_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {Y T V W : Scheme.{u}}
    (e : Y ⟶ T) (j : V ⟶ T) (eV : W ⟶ V) (a : W ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (sq : IsPullback eV a j e)
    (n : ℤ) (hbc : BaseChangeProperty Λ e n)
    (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (((j)_*[ModuleCat.{u + 1} Λ]).obj J))) ≫
        R+((a)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
            D+((eV)^*[ModuleCat.{u + 1} Λ]).map
              ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
                (DerivedCategory.Plus.singleFunctor _ 0).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J))))) := by
  have hf := open_injective_coefficient_lower_comparison_factorization Λ e j eV a wa sq n J
  rw [hf, Functor.map_comp]
  let G := ((j)_*[ModuleCat.{u + 1} Λ])
  have hu : IsIso (G.rightDerivedPlusSingleUnit J) := by
    let M := (HomotopyCategory.Plus.singleFunctor _ 0).obj J
    have (k : ℤ) : Injective (M.obj.as.X k) := by
      by_cases hk : k = 0
      · subst k
        exact Injective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 J).symm
          inferInstance
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk).injective
    have : IsIso (G.rightDerivedFunctorPlusUnith.app M) := inferInstance
    dsimp [Functor.rightDerivedPlusSingleUnit]
    infer_instance
  have hb := hbc j eV a sq J
  have hb' : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj J))) := by
    simpa [baseChangeHomologyMap, baseChangeHomologyNatTrans,
      baseChangeSourceFunctor, baseChangeTargetFunctor] using hb
  infer_instance


end AlgebraicGeometry.Etale
