/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.LocalizedPullbackPerfectModel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Derived pullback preserves perfect complexes

Source: Stacks Project, perfect.tex, Tag 09UA.
-/

@[expose] public section

universe u w
open CategoryTheory
namespace AlgebraicGeometry

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the unit sheaf across the two open-site equivalences and pullback. -/
private noncomputable def localizedPullbackUnitIso {T X : Scheme.{u}} (g : T ⟶ X)
    (U : X.Opens) :
    (Scheme.Modules.localizedPullback g U).obj
        (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)) ≅
      SheafOfModules.unit ((moduleRings T.toRingedSpace).over (g ⁻¹ᵁ U)) := by
  have : PreservesLimit (Functor.empty.{0} U.toScheme.Opens)
      (TopologicalSpace.Opens.map (g.resLE U (g ⁻¹ᵁ U) le_rfl).base) :=
    preservesTerminal_of_iso _
      ((TopologicalSpace.Opens.map (g.resLE U (g ⁻¹ᵁ U) le_rfl).base).mapIso
        (terminalIsoIsTerminal isTerminalTop) ≪≫
        (terminalIsoIsTerminal isTerminalTop).symm)
  have : (TopologicalSpace.Opens.map (g.resLE U (g ⁻¹ᵁ U) le_rfl).base).Final :=
    inferInstance
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (g.resLE U (g ⁻¹ᵁ U) le_rfl).toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  exact (Scheme.Modules.overEquiv (g ⁻¹ᵁ U)).inverse.mapIso
    ((Scheme.Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).mapIso
      (U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace)) ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit
        (g.resLE U (g ⁻¹ᵁ U) le_rfl).toRingCatSheafHom)) ≪≫
    (g ⁻¹ᵁ U).sheafOfModulesEquivOverInverseUnit (moduleRings T.toRingedSpace)

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Localized pullback carries finite free modules to finite free modules. -/
private theorem localizedPullbackFree {T X : Scheme.{u}} (g : T ⟶ X)
    (U : X.Opens) (m : ℕ) :
    Nonempty ((Scheme.Modules.localizedPullback g U).obj
        (SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin m))) ≅
      SheafOfModules.free (R := (moduleRings T.toRingedSpace).over (g ⁻¹ᵁ U))
        (ULift.{u} (Fin m))) := by
  let F := Scheme.Modules.localizedPullback g U
  have : F.IsLeftAdjoint := by
    dsimp [F, Scheme.Modules.localizedPullback]
    infer_instance
  exact ⟨(asIso (sigmaComparison F
    (fun _ : ULift.{u} (Fin m) ↦
      SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
    Sigma.mapIso (fun _ ↦ localizedPullbackUnitIso g U)⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Boundedness and the finite-free retract equations survive ordinary pullback. -/
private theorem localizedPullbackStrictlyPerfect {T X : Scheme.{u}} (g : T ⟶ X)
    (U : X.Opens)
    (K : CochainComplex (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : Scheme.IsStrictlyPerfect X U K) :
    Scheme.IsStrictlyPerfect T (g ⁻¹ᵁ U)
      (((Scheme.Modules.localizedPullback g U).mapHomologicalComplex (.up ℤ)).obj K) := by
  let F := Scheme.Modules.localizedPullback g U
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  constructor
  · exact ⟨a, b, fun n hn ↦ F.map_isZero (hb n hn)⟩
  · intro n
    obtain ⟨m, ι, π, hιπ⟩ := hp n
    obtain ⟨e⟩ := localizedPullbackFree g U m
    refine ⟨m, F.map ι ≫ e.hom, e.inv ≫ F.map π, ?_⟩
    change (F.map ι ≫ e.hom) ≫ e.inv ≫ F.map π = 𝟙 (F.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hιπ]
    exact F.map_id _

/-- Derived pullback of a perfect complex is perfect.
Source: Stacks Project, perfect.tex, Tag 09UA
(blueprint: lem-pc-derived-pullback-perfect).
Proof: at t choose a strictly perfect local model K on a neighbourhood U of g(t).
The constructed functor `Scheme.Modules.localizedPullback g U` carries K to a complex
on the localized site of the inverse-image open. Its unit-sheaf isomorphism and
preservation of coproducts identify every pulled finite free module with a finite free
module of the same rank. Applying the functor to the given retract maps and transporting
through this isomorphism preserves their splitting equation. Additivity preserves the
zero terms outside the original finite interval. Thus the pulled complex is strictly
perfect. The proved `localizedPullback_perfectModel_iso` identifies its derived object
with the restriction of Lg* E, using the existing restriction comparison and
`flatComplexDerivedPullback` on the transported model. This supplies the local witness
at t, including empty schemes and zero complexes. -/
theorem derivedPullback_preserve_perfect {T X : Scheme.{u}} (g : T ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect T ((derivedPullback g).obj E) := by
  intro t
  obtain ⟨U, ht, K, hK, ⟨e⟩⟩ := hE (g t)
  refine ⟨g ⁻¹ᵁ U, ht,
    ((Scheme.Modules.localizedPullback g U).mapHomologicalComplex (.up ℤ)).obj K,
    localizedPullbackStrictlyPerfect g U K hK, ?_⟩
  exact localizedPullback_perfectModel_iso g U E K hK e

end AlgebraicGeometry
