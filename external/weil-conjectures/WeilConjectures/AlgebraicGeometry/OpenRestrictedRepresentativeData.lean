/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
/-! # A literal restricted K-flat representative -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- Literal open restriction represents derived open pullback and has invertible
pullback counit along any morphism. Source: Stacks Project, Tags 06YB and 0D5U.
(blueprint: lem-pc-open-restricted-representative-data).

Proof: open restriction preserves K-flatness by the stalk criterion. Transport
the K-flat counit isomorphism from derivedPullback_spec to the specified counit
by uniqueness of left derived functors. Uniqueness of left adjoints identifies
tensor pullback along U.ι with literal restriction. Apply this isomorphism to
complexes and localization. Compose with the inverse specified counit along U.ι,
the quotientCompQhIso factors, and derived pullback of eP.
The construction applies to zero complexes and empty opens without extra choices. -/
theorem exists_open_restricted_representative_data
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (U : X.Opens) (q : T ⟶ U.toScheme)
    (K : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (eP : DerivedCategory.Q.obj P ≅ K) :
    let Q : CochainComplex
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
      ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
    ∃ (_hQ : Q.IsKFlatTensor)
      (_hcQ : IsIso ((counit q).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
      (_eQ : DerivedCategory.Q.obj Q ≅ (derivedPullback U.ι).obj K), True := by
  classical
  dsimp only
  let Q : CochainComplex
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
      ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  have hQ : Q.IsKFlatTensor := isKFlat_restrict U.ι P hP
  have hcQ := counit_isIso_kFlat q Q hQ
  let T : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.restrictFunctor U.ι
  let θ : T ≅ R :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  have : T.Additive := tensorPullbackAdditive U.ι
  have : R.Additive := Functor.additive_of_iso θ
  have hj := counit_isIso_kFlat U.ι P hP
  have := hj
  let eQ : DerivedCategory.Q.obj Q ≅ (derivedPullback U.ι).obj K :=
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex θ (.up ℤ)).app P).symm ≪≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))).symm.app
          ((T.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
      (asIso ((counit U.ι).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
      (derivedPullback U.ι).mapIso
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings X.toRingedSpace))).app P) ≪≫
      (derivedPullback U.ι).mapIso eP
  exact ⟨hQ, hcQ, eQ, trivial⟩

end AlgebraicGeometry.SingleComplexBaseChange
