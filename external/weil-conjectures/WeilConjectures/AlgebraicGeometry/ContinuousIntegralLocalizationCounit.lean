/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # Localization acts identically on rational modules -/

@[expose] public section

universe u v
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A scalar telescope of an object on which the scalar is invertible has an
invertible zeroth colimit leg.
Source: universal property of the localization telescope.
(auxiliary; not a blueprint node) -/
theorem integralLocalization_zero_isIso (ℓ : ℕ)
    {C : Type*} [Category C] [Preadditive C] (K : C) [IsIso (ℓ • 𝟙 K)]
    (c : Cocone (Mod.smulSequence K ℓ)) (hc : IsColimit c)
    [IsIso (ℓ • 𝟙 c.pt)] : IsIso (c.ι.app 0) := by
  let t : End K := .of (inv (ℓ • 𝟙 K))
  let d : Cocone (Mod.smulSequence K ℓ) :=
    Mod.smulSequenceCocone ℓ (fun n ↦ (t ^ n).asHom) fun n ↦ by
      rw [← Category.id_comp (t ^ (n + 1)).asHom, ← Preadditive.nsmul_comp, pow_succ,
        End.mul_asHom, ← Category.assoc]
      simp [t]
  have hz : d.ι.app 0 = 𝟙 K := rfl
  let g := hc.desc d
  have hg : c.ι.app 0 ≫ g = 𝟙 K := by simp only [g, hc.fac, hz]
  refine ⟨⟨g, hg, ?_⟩⟩
  apply hc.hom_ext
  intro n
  simp only [Functor.const_obj_obj, Category.comp_id]
  exact
    integralLocalization_coconeLegs ℓ c c (g ≫ c.ι.app 0)
      (by
        change c.ι.app 0 ≫ (g ≫ c.ι.app 0) = c.ι.app 0
        rw [← Category.assoc, hg]
        exact Category.id_comp _) n

/-- Restriction followed by extension of integral coefficients has counit an
isomorphism on every rational module.
Source: Bhatt--Scholze, Lemma 6.8.2, localization at ℓ.
(auxiliary; not a blueprint node)
Proof. The restricted rational module has invertible ℓ. Its localization telescope
therefore has invertible zeroth leg. This leg is the extension unit; the adjunction
triangle then makes the restricted counit invertible. Restriction is faithful and
both module categories are abelian, so it reflects this isomorphism. -/
theorem integralScalarCounit_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    IsIso ((Mod.extendRestrictAdjunction
      (coefficientMap (integralScalarMap ℓ E) X)).counit.app P) := by
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) := inferInstance
  let a := coefficientMap (integralScalarMap ℓ E) X
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a
  let adj := Mod.extendRestrictAdjunction a
  have := module_nsmul_isIso ℓ E X P
  have := mappedScalar_isIso ℓ U P
  let c := integralModuleLocalizationCocone ℓ E X (U.obj P)
  have := module_nsmul_isIso ℓ E X ((Mod.extendScalars a).obj (U.obj P))
  have := mappedScalar_isIso ℓ U ((Mod.extendScalars a).obj (U.obj P))
  obtain ⟨hc⟩ := integralModuleLocalization_isColimit ℓ E X (U.obj P)
  have : IsIso (ℓ • 𝟙 c.pt) := by
    change IsIso (ℓ • 𝟙 (U.obj ((Mod.extendScalars a).obj (U.obj P))))
    infer_instance
  have hu : IsIso (adj.unit.app (U.obj P)) := by
    have hz := integralLocalization_zero_isIso ℓ (U.obj P) c hc
    have heq : c.ι.app 0 = adj.unit.app (U.obj P) := by
      simp [c, integralModuleLocalizationCocone, scalarLocalizationUnitCocone, adj, a]
    rwa [heq] at hz
  have hcounit : IsIso (U.map (adj.counit.app P)) := by
    have htriangle := adj.right_triangle_components P
    have : IsIso (adj.unit.app (U.obj P) ≫ U.map (adj.counit.app P)) := by
      rw [htriangle]
      exact ⟨⟨𝟙 _, by simp [U]⟩⟩
    exact IsIso.of_isIso_comp_left (adj.unit.app (U.obj P)) _
  change IsIso (adj.counit.app P)
  have : Mono (adj.counit.app P) :=
    Functor.mono_of_mono_map U (inferInstance : Mono (U.map (adj.counit.app P)))
  have : Epi (adj.counit.app P) :=
    Functor.epi_of_epi_map U (inferInstance : Epi (U.map (adj.counit.app P)))
  exact isIso_of_mono_of_epi (adj.counit.app P)

end AlgebraicGeometry.ProEtale.CondensedRing
