/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # The scalar telescope computed in complexes -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The termwise extension unit presents extension of a complex as the scalar telescope.
Source: Bhatt--Scholze, Lemma 6.8.2, applied degreewise.
(auxiliary; not a blueprint node).
Proof. Form the unit cocone for the adjunction on complexes. Evaluation identifies
its zeroth leg with the module extension unit. Multiplication by ℓ is invertible
on every extended term, so the zeroth leg determines all legs. The module telescope
is colimiting in each degree; evaluation jointly reflects colimits of complexes. -/
theorem integralComplexLocalization_colimit (X : Scheme.{u})
    (C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) ℤ) :
    ∃ c : Cocone (Mod.smulSequence C ℓ), Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (coefficientMap (integralScalarMap ℓ E) X)).mapHomologicalComplex (.up ℤ)).obj
          (((Mod.extendScalars
            (coefficientMap (integralScalarMap ℓ E) X)).mapHomologicalComplex (.up ℤ)).obj C),
        c.ι.app 0 ≫ e.hom =
          ((Mod.extendRestrictAdjunction
            (coefficientMap (integralScalarMap ℓ E) X)).mapHomologicalComplex
            (.up ℤ)).unit.app C := by
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let L := Mod.extendScalars φ
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let LC := L.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let adj := (Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)
  have : ∀ n, IsIso ((ℓ • 𝟙 (LC.obj C)).f n) := fun n ↦ by
    change IsIso (ℓ • 𝟙 (L.obj (C.X n)))
    exact module_nsmul_isIso ℓ E X _
  have : IsIso (ℓ • 𝟙 (LC.obj C)) := HomologicalComplex.Hom.isIso_of_components _
  let c := scalarLocalizationUnitCocone ℓ adj C
  refine ⟨c, ⟨?_⟩, Iso.refl _, ?_⟩
  · apply HomologicalComplex.isColimitOfEval _ c
    intro n
    let ev := HomologicalComplex.eval
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) (.up ℤ) n
    let σ := Mod.smulSequenceCompIso ev C ℓ
    let d := (Cocone.precompose σ.inv).obj (ev.mapCocone c)
    let cn := integralModuleLocalizationCocone ℓ E X (C.X n)
    let hn := Classical.choice (integralModuleLocalization_isColimit ℓ E X (C.X n))
    have := module_nsmul_isIso ℓ E X (L.obj (C.X n))
    have : IsIso (ℓ • 𝟙 cn.pt) := mappedScalar_isIso ℓ U _
    have hzero : d.ι.app 0 ≫ 𝟙 _ = cn.ι.app 0 := by
      simp only [Mod.smulSequenceCompIso, Functor.comp_obj, NatIso.ofComponents_inv_app,
        Iso.refl_inv, Adjunction.mapHomologicalComplex, Functor.id_obj,
        scalarLocalizationUnitCocone, Functor.const_obj_obj, Cocone.precompose_obj_pt,
        Functor.mapCocone_pt, Cocone.precompose_obj_ι, NatTrans.comp_app,
        Functor.mapCocone_ι_app, pow_zero, End.one_asHom, CategoryTheory.Functor.map_id,
        Category.comp_id, integralModuleLocalizationCocone, d, σ, c, adj, cn]
      change 𝟙 (C.X n) ≫ (Mod.extendRestrictAdjunction φ).unit.app (C.X n) =
        (Mod.extendRestrictAdjunction φ).unit.app (C.X n)
      exact Category.id_comp _
    have ei : d ≅ cn := Cocone.ext (Iso.refl _)
      (integralLocalization_coconeLegs ℓ d cn (𝟙 _) hzero)
    have hd : IsColimit d := hn.ofIsoColimit ei.symm
    exact IsColimit.precomposeHomEquiv σ.symm (ev.mapCocone c) hd
  · simp [c, scalarLocalizationUnitCocone, adj, φ]

end AlgebraicGeometry.ProEtale.CondensedRing
