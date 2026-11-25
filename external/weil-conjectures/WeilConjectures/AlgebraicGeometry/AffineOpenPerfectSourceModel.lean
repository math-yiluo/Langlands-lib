/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel

import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Perfect source models on affine opens

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-perfect-source-model).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exact realization of open pullback preserves perfectness. -/
private theorem perfect_exact_pullback {Y X : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (θ : F ≅ Modules.tensorPullback g)
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    IsPerfect Y (F.mapDerivedCategory.obj E) := by
  classical
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let T : B ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Modules.tensorPullback g
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    G, hG, hGmap, hGadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec g
  have h : G = T := CategoryTheory.Functor.ext hG (fun M N a ↦ hGmap a)
  subst G
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have : (derivedPullback g).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback g ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback g) ε
      T.mapDerivedCategoryFactorsh.hom W
  let c := (Functor.mapDerivedCategoryNatIso θ).app E ≪≫ i.symm.app E
  have hp := derivedPullback_preserve_perfect g E hE
  intro y
  obtain ⟨V, hy, K, hK, ⟨iK⟩⟩ := hp y
  exact ⟨V, hy, K, hK, ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings Y.toRingedSpace) V).mapDerivedCategory.mapIso c ≪≫ iK⟩⟩

/-- An exact equivalence transfers the size of a chosen derived localization. -/
private theorem localization_on_source {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  let : HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let d := e.mapDerivedCategory
  let : LocallySmall.{w} (DerivedCategory C) :=
    (locallySmall_congr d).mpr inferInstance
  exact ⟨(HomologicalComplex.quasiIso C (.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The perfect source has a bounded finite-projective model under any realization
of the explicit affine sheafification functor.
Source: Stacks Project, Tag 08EB and Tag 06Z0.
(blueprint: lem-sc-affine-open-perfect-source-model).

Proof: Construct the exact module equivalence from the spectrum to the localized
open site using isoSpec and overEquiv. Its derived equivalence transports local
smallness, yielding a localization on the spectrum in universe w; choose the
localizations on its opens by nonempty_derivedOpenLocalization. Restriction followed
by the inverse equivalence is ordinary pullback along Spec Gamma(U,O_X) → U → X.
Uniqueness of left derived functors identifies its exact derived functor with
derivedPullback, so derivedPullback_preserve_perfect proves perfectness of the
transported source. Perfectness supplies quasi-coherent cohomology. Apply
perfect_iff_affine_bounded_projective to this object to obtain P with the required
bounds and finite projective terms. The factorization of the exact equivalence
through Q and mapHomologicalComplexCompIso identify its transported tilde complex
with affinePerfectSheafification(P). Compose this comparison, the given comparison
at P, the model isomorphism, and the derived counit to recover the restricted E.
All constructions also apply to the empty open; no point or nonzero ring is chosen.
No support or scalar compatibility is asserted here. -/
theorem affine_open_perfect_source_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory X) (hE : X.IsPerfect E.obj)
    (U : X.Opens) (hU : IsAffineOpen U) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
        (∀ i : ℤ, Module.Finite A (P.X i)) ∧
        (∀ i : ℤ, Module.Projective A (P.X i)) ∧
        Nonempty (F.obj (DerivedCategory.Q.obj P) ≅ R.obj E.obj) := by
  classical
  dsimp only
  intro F ⟨hF⟩
  let A := X.presheaf.obj (.op U)
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let S := SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let f := Modules.restrictFunctor hU.isoSpec.hom
  let g := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{u}).Modules := CategoryTheory.Equivalence.mk f g
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [A]) ≪≫
        Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let e₀ : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : e₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e₀.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : r.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨hS⟩ := localization_on_source e₀
  let := hS
  obtain ⟨hSO⟩ := nonempty_derivedOpenLocalization (Spec A)
  let := hSO
  let eD := e₀.mapDerivedCategory
  let H := r ⋙ e₀.inverse
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits H := comp_preservesFiniteColimits _ _
  let j := hU.isoSpec.inv ≫ U.ι
  let θ : H ≅ Modules.tensorPullback j :=
    (Functor.associator r (Modules.overEquiv U).functor g).symm ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U) g ≪≫
      (Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm ≪≫
      Modules.restrictFunctorIsoPullback j ≪≫
      ((Modules.nonempty_tensorPullbackAdjunction j).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction j)).symm
  have hpH : IsPerfect (Spec A) (H.mapDerivedCategory.obj E.obj) :=
    perfect_exact_pullback j H θ E.obj hE
  let C := eD.inverse.obj (r.mapDerivedCategory.obj E.obj)
  let c : H.mapDerivedCategory.obj E.obj ≅ C :=
    ((Functor.mapDerivedCategoryCompIso r e₀.inverse).app E.obj).symm
  have hpC : IsPerfect (Spec A) C := by
    intro x
    obtain ⟨V, hx, K, hK, ⟨iK⟩⟩ := hpH x
    exact ⟨V, hx, K, hK, ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings (Spec A).toRingedSpace) V).mapDerivedCategory.mapIso c.symm ≪≫ iK⟩⟩
  let EC : schemeDerivedQCohCategory (Spec A) :=
    ⟨C, schemeDerivedQCohProperty_of_isPerfect (Spec A) C hpC⟩
  obtain ⟨P, hb, hf, hp, ⟨hCP⟩⟩ :=
    (perfect_iff_affine_bounded_projective.{u, w} A EC).mp hpC
  let T : ModuleCat.{u} A ⥤ S := tilde.functor A
  have : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  have : T.Additive := inferInstanceAs (tilde.functor A).Additive
  let cmp : (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ eD.functor ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
        e₀.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ e₀.functor)) (.up ℤ)) _
  refine ⟨P, hb, hf, hp, ?_⟩
  exact ⟨hF.app P ≪≫ (cmp.app P).symm ≪≫
    eD.functor.mapIso hCP.symm ≪≫ eD.counitIso.app _⟩

end AlgebraicGeometry.Scheme
