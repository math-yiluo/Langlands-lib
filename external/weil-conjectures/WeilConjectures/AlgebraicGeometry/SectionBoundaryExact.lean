/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Exactness of the canonical boundary on global sections

Source: Stacks Project, Cohomology, Tag 01DZ.
(blueprint: lem-sc-module-section-boundary-exact).
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.RingedSpace
universe u wC wD

/-- The canonical connecting map, preceded by the degree-zero comparison from sections.
Source: Stacks Project, Cohomology, Tag 01DZ.
(blueprint: lem-sc-module-section-boundary-exact). -/
noncomputable def moduleSectionBoundary (X : RingedSpace.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X).obj.obj (Opposite.op ⊤)))]
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) (hS : S.ShortExact) :
    (globalSectionsFunctor X).obj S.X₃ ⟶ (moduleCohomology X 1).obj S.X₁ :=
  letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  (globalSectionsFunctor X).toRightDerivedZero.app S.X₃ ≫
    moduleCohomologyBoundary X S hS 0

private theorem section_boundary_exact
    {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{wC} C]
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory.{wD} D]
    (v : C ⥤ D) [v.Additive] [PreservesFiniteLimits v]
    (S : ShortComplex C) (hS : S.ShortExact) :
    let T := (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      hS.singleTrianglePlus
    let e (n : ℕ) := v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
    let δ := DerivedCategory.HomologySequence.δ T 0 1 (by norm_num)
    let b := (e 0).inv.app S.X₃ ≫ δ ≫ (e 1).hom.app S.X₁
    ∃ w : (v.rightDerived 0).map S.g ≫ b = 0,
      (ShortComplex.mk ((v.rightDerived 0).map S.g) b w).Exact := by
  let T := (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
    hS.singleTrianglePlus
  have hT : T ∈ distTriang _ := Functor.map_distinguished _ _
    hS.singleTrianglePlus_distinguished
  let e (n : ℕ) := v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  let δ := DerivedCategory.HomologySequence.δ T 0 1 (by norm_num)
  have he := DerivedCategory.HomologySequence.exact₃ T hT 0 1 (by norm_num)
  let b := (e 0).inv.app S.X₃ ≫ δ ≫ (e 1).hom.app S.X₁
  have w : (v.rightDerived 0).map S.g ≫ b = 0 := by
    refine ((e 0).inv.naturality_assoc S.g _).trans ?_
    refine (congrArg ((e 0).inv.app S.X₂ ≫ ·)
      (DerivedCategory.HomologySequence.comp_δ_assoc T hT 0 1 (by norm_num)
        ((e 1).hom.app S.X₁))).trans ?_
    erw [zero_comp, comp_zero]
  refine ⟨w, ?_⟩
  apply (ShortComplex.exact_iff_of_iso ?_).1 he
  exact ShortComplex.isoMk ((e 0).app S.X₂) ((e 0).app S.X₃) ((e 1).app S.X₁)
    ((e 0).hom.naturality S.g).symm (Iso.hom_inv_id_app_assoc (e 0) S.X₃ _)

/-- A section has zero canonical boundary precisely when it lifts through the quotient.
Source: Stacks Project, Cohomology, Tag 01DZ.
(blueprint: lem-sc-module-section-boundary-exact).
Proof: The image of the short exact sequence's canonical triangle under derived global
sections is distinguished. Its homology sequence is exact at degree zero of the quotient.
Transport that exactness through the single-complex comparison and the isomorphism from
sections to zeroth derived global sections. Exactness in modules is exactness of the
underlying functions, giving precisely the asserted existence of a lifting section. -/
theorem moduleSectionBoundary_eq_zero_iff (X : RingedSpace.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X).obj.obj (Opposite.op ⊤)))]
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) (hS : S.ShortExact)
    (s : (globalSectionsFunctor X).obj S.X₃) :
    moduleSectionBoundary X S hS s = 0 ↔
      ∃ t : (globalSectionsFunctor X).obj S.X₂, (globalSectionsFunctor X).map S.g t = s := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  have : PreservesFiniteLimits (globalSectionsFunctor X) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X) (Opposite.op ⊤)))
  let b := moduleCohomologyBoundary X S hS 0
  have h := section_boundary_exact (globalSectionsFunctor X) S hS
  change ∃ w : ((globalSectionsFunctor X).rightDerived 0).map S.g ≫ b = 0,
    (ShortComplex.mk (((globalSectionsFunctor X).rightDerived 0).map S.g) b w).Exact at h
  obtain ⟨w, hex⟩ := h
  change ((globalSectionsFunctor X).toRightDerivedZero.app S.X₃ ≫ b) s = 0 ↔
    ∃ t : (globalSectionsFunctor X).obj S.X₂, (globalSectionsFunctor X).map S.g t = s
  have hsec : (globalSectionsFunctor X).map S.g ≫
      ((globalSectionsFunctor X).toRightDerivedZero.app S.X₃ ≫ b) = 0 := by
    rw [(globalSectionsFunctor X).toRightDerivedZero.naturality_assoc S.g]
    rw [w, comp_zero]
  have hunit : IsIso ((globalSectionsFunctor X).toRightDerivedZero.app S.X₂) := inferInstance
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex
      ((globalSectionsFunctor X).toRightDerivedZero.app S.X₃ s) hs
    refine ⟨inv ((globalSectionsFunctor X).toRightDerivedZero.app S.X₂) t, ?_⟩
    apply (ModuleCat.mono_iff_injective ((globalSectionsFunctor X).toRightDerivedZero.app S.X₃)).mp
      (inferInstance : Mono ((globalSectionsFunctor X).toRightDerivedZero.app S.X₃))
    have hn := congrArg (fun f ↦ f (inv ((globalSectionsFunctor X).toRightDerivedZero.app S.X₂) t))
      ((globalSectionsFunctor X).toRightDerivedZero.naturality S.g)
    simp only [ConcreteCategory.comp_apply, IsIso.inv_hom_id_apply] at hn
    exact hn.trans ht
  · rintro ⟨t, rfl⟩
    exact congrArg (fun f ↦ f t) hsec

end AlgebraicGeometry.RingedSpace
