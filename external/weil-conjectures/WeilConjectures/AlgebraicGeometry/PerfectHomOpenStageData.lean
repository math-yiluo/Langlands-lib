/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a chosen localization along an exact equivalence of abelian categories.
This is the localization construction in `SchemeIsoDerivedLocalizations`, specialized
to the module-sheaf universe; its helper there is private. -/
private theorem hasDerivedCategory_of_equivalence {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact open restriction is derived pullback, hence preserves perfectness (Stacks 09UA). -/
private theorem perfect_exactOpenRestriction (Y : Scheme.{u}) (A : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))]
    [∀ V : A.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings A.toScheme.toRingedSpace).over V))]
    (R' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))
    [R'.Additive] [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
    (hR' : R' = SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) A ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over A))
        (D := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))
        (Modules.overEquiv A))
    (E : schemeDerivedCategory Y) (hE : IsPerfect Y E) :
    IsPerfect A.toScheme (R'.mapDerivedCategory.obj E) := by
  classical
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let C := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace)
  let T : B ⥤ C := Modules.tensorPullback A.ι
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec A.ι
  have h : F = T := CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let η : T ≅ Modules.restrictFunctor A.ι :=
    (Modules.nonempty_tensorPullbackAdjunction A.ι).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction A.ι) ≪≫
        (Modules.restrictFunctorIsoPullback A.ι).symm
  let θ : R' ≅ T := eqToIso hR' ≪≫ Modules.overFunctorEquiv A ≪≫ η.symm
  have : Limits.PreservesFiniteLimits T :=
    Limits.preservesFiniteLimits_of_natIso θ
  have : Limits.PreservesFiniteColimits T :=
    Limits.preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have : (derivedPullback A.ι).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback A.ι ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback A.ι) ε
      T.mapDerivedCategoryFactorsh.hom W
  let c := (Functor.mapDerivedCategoryNatIso θ).app E ≪≫ i.symm.app E
  have hp := derivedPullback_preserve_perfect A.ι E hE
  intro x
  obtain ⟨V, hx, K, hK, ⟨iK⟩⟩ := hp x
  refine ⟨V, hx, K, hK, ?_⟩
  exact ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings A.toScheme.toRingedSpace) V).mapDerivedCategory.mapIso c ≪≫ iK⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem perfect_shift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E : schemeDerivedCategory X} (hE : IsPerfect X E) (n : ℤ) :
    IsPerfect X (E⟦n⟧) := by
  intro x
  obtain ⟨U, hx, K, ⟨⟨a, b, hb⟩, hf⟩, ⟨eK⟩⟩ := hE x
  refine ⟨U, hx, K⟦n⟧, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨a - n, b - n, fun i hi ↦ ?_⟩
    exact hb (i + n) (by omega)
  · exact fun i ↦ hf (i + n)
  · let F := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    exact ⟨(F.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso eK ≪≫
      ((DerivedCategory.Q.commShiftIso n).app K).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicitly restricted objects are perfect on an open subscheme, including
all shifts. Source: Stacks Project, Tags 09UA and 08CM.
(blueprint: lem-pc-perfect-hom-open-stage-data).
Proof: Transport each localized module category through `Modules.overEquiv`
to the already supplied derived category on its open scheme. This constructs
its localization as the composite of the exact equivalence on complexes with Q.
Exact restriction agrees with derived pullback by uniqueness of the left-derived
functor. Derived pullback preserves perfectness. Shift the local strictly perfect
models, translating their bounds by n and retaining each term's retract maps.
An empty open has no points at which perfectness must be checked. -/
theorem perfect_hom_open_stage_data
    (Y : Scheme.{u})
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ B : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over B))]
    (B : Y.Opens) (P Q : schemeDerivedCategory Y)
    (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) (n : ℤ) :
    ∃ hcat : ∀ T : B.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings B.toScheme.toRingedSpace).over T)),
      let := hcat
      B.toScheme.IsPerfect (((schemeMVDerivedRestriction Y B).obj P)⟦-n⟧) ∧
      B.toScheme.IsPerfect ((schemeMVDerivedRestriction Y B).obj Q) := by
  classical
  let hcat : ∀ T : B.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings B.toScheme.toRingedSpace).over T)) :=
    fun T ↦ by
      letI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace)) := inferInstance
      let e : SheafOfModules.{u} ((moduleRings B.toScheme.toRingedSpace).over T) ≌
          SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace) := Modules.overEquiv T
      exact Classical.choice (hasDerivedCategory_of_equivalence e)
  refine ⟨hcat, ?_⟩
  let := hcat
  have hp := perfect_exactOpenRestriction Y B (schemeOpenRestriction Y B) rfl P hP
  have hq := perfect_exactOpenRestriction Y B (schemeOpenRestriction Y B) rfl Q hQ
  exact ⟨perfect_shift B.toScheme hp (-n), hq⟩

end AlgebraicGeometry.Scheme
