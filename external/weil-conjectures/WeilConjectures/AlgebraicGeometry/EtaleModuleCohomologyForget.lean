/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic

/-!
# Module cohomology and underlying abelian cohomology

Source: Stacks Project, Cohomology on Sites, Tag 03FD, applied to a constant ring.
(blueprint: lem-weil-pbc-etale-module-cohomology-forget).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian sheaf functor is a left adjoint, hence preserves colimits. -/
theorem moduleSheafForgetIsLeftAdjoint (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).IsLeftAdjoint := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
    infer_instance
  let e : CategoryTheory.Sheaf.composeAndSheafify Y.smallEtaleTopology U ≅
      sheafCompose Y.smallEtaleTopology U :=
    Functor.isoWhiskerLeft (sheafCompose Y.smallEtaleTopology U)
      (asIso (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).counit) ≪≫
      (sheafCompose Y.smallEtaleTopology U).rightUnitor
  exact ((Sheaf.adjunction Y.smallEtaleTopology
    (Adjunction.ofIsLeftAdjoint U)).ofNatIsoLeft e).isLeftAdjoint

/-- Forgetting the module structure commutes naturally with cohomology of a sheaf
placed in degree zero. This comparison has no compactness or colimit hypothesis.
Source: Stacks Project, Tag 03FD and its proof.
(blueprint: lemma-cohomology-modules-underlying-abelian).

Proof:
1. The coefficient forgetful functor is both a left and a right adjoint, using
restriction and coextension or extension of scalars along `Z → Λ` and the equivalence
of integer modules with abelian groups. Its induced sheaf functor is also both a left
and a right adjoint, using the sheafification adjunction. Thus both functors are exact.
2. Evaluate at the terminal identity étale object. Evaluation commutes with forgetting
coefficients by definition, and the two global-sections/evaluation isomorphisms give
`Γ_modules ⋙ forget ≅ sheafForget ⋙ Γ_abelian`.
3. The underlying sheaf functor sends module injectives to abelian-global-sections
acyclic objects by `lemma-cohomology-modules-underlying-abelian`. Apply the source
library's invertibility theorem for bounded-below derived base change. Its homology
comparison gives a natural isomorphism of the classical right derived functors.
4. For both coefficient categories, the proved plus-derived compatibility and the
single-functor homology isomorphism identify classical derived global sections with
`Etale.cohomology` on degree-zero sheaves. Compose these natural isomorphisms with the
base-change isomorphism from step 3. -/
theorem nonempty_etaleModuleCohomology_forgetIso
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (q : ℕ) :
    Nonempty
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
          Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)) ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
        sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
          (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
            Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ))) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : U.Additive := by infer_instance
  have : PreservesFiniteLimits U := by infer_instance
  have : U.IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom Λ)).isLeftAdjoint
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} U :=
    (Adjunction.ofIsLeftAdjoint U).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits U :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} U
  let S := sheafCompose Y.smallEtaleTopology U
  let GM := Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let GA := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : S.IsLeftAdjoint := moduleSheafForgetIsLeftAdjoint Y Λ
  have : S.Additive := by
    constructor
    intro X Z f g
    ext W
    rfl
  have : S.IsRightAdjoint := by
    have : U.IsRightAdjoint := by
      change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsRightAdjoint
      have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsRightAdjoint :=
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
          (Int.castRingHom Λ)).isRightAdjoint
      infer_instance
    infer_instance
  have : PreservesFiniteLimits S := by infer_instance
  have : PreservesFiniteColimits S := by infer_instance
  let V : Y.Etale := Etale.mk (𝟙 Y)
  have hV : IsTerminal V := MorphismProperty.Over.mkIdTerminal @Etale Y
  let e : GM ⋙ U ≅ S ⋙ GA :=
    Functor.isoWhiskerRight
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hV) U ≪≫
      Functor.isoWhiskerLeft S
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1} hV).symm
  have hacy (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G] :
      GA.rightAcyclic (S.obj G) :=
    fun n ↦ isZero_rightDerived_globalSections_forget_of_injective Y Λ G n
  have := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (G := GM) (G' := GA) (β := S) (γ := U) e hacy
  have : IsIso (Functor.rightDerivedBaseChange
      (G := GM) (G' := GA) (β := S) (γ := U) e.hom q) := by
    unfold Functor.rightDerivedBaseChange
    infer_instance
  let em : DerivedCategory.singleFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ) ≅ GM.rightDerived q :=
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
      (Functor.isoWhiskerRight GM.rightDerivedFunctorPlusCompatibility.symm
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (q : ℤ))) ≪≫
      GM.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  let ea : DerivedCategory.singleFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ) ≅ GA.rightDerived q :=
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
      (Functor.isoWhiskerRight GA.rightDerivedFunctorPlusCompatibility.symm
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ))) ≪≫
      GA.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  exact ⟨Functor.isoWhiskerRight em U ≪≫
    asIso (Functor.rightDerivedBaseChange
      (G := GM) (G' := GA) (β := S) (γ := U) e.hom q) ≪≫ Functor.isoWhiskerLeft S ea.symm⟩

end AlgebraicGeometry.Scheme
