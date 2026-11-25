/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic

/-!
# Flat localization of the second derived tensor factor

Source: Stacks Project, More on Algebra, Tag 06Y6, flat cohomology base change and
comparison-map (blueprint: lem-pc-derived-tensor-flat-second-localization).
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory

namespace RingTensorCohomology

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of flat cohomology base change for arbitrary R-chain maps. -/
private theorem baseChangeMap_naturality
    (R B C : Type v) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    (hflat : (algebraMap B C).Flat) (i : ℤ)
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L) :
    (ModuleCat.extendScalars (algebraMap B C)).map
        (HomologicalComplex.homologyMap ((extend R B).map f) i) ≫
        baseChangeMap R B C hflat L i =
      baseChangeMap R B C hflat K i ≫
        HomologicalComplex.homologyMap ((extend R C).map f) i := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  dsimp only [baseChangeMap, flatHomologyMap]
  rw [← Category.assoc]
  erw [ShortComplex.mapHomologyIso_inv_naturality]
  change ((((extend R B).obj K).sc i).mapHomologyIso
      (ModuleCat.extendScalars (algebraMap B C))).inv ≫
      HomologicalComplex.homologyMap ((extend B C).map ((extend R B).map f)) i ≫
        HomologicalComplex.homologyMap ((extendCompIso R B C).hom.app L) i = _
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  exact congrArg (fun g ↦ HomologicalComplex.homologyMap g i)
    ((extendCompIso R B C).hom.naturality f)

/-- Flat localization of the second factor, including naturality, both scalar actions,
and compatibility with the comparison map of Stacks Tag 06Y6.

The source and target use the models in `def-pc-ring-tensor-cohomology`. Extension of
scalars is written with C on the left of the tensor product, using the canonical symmetry
C tensor-over-B H = H tensor-over-B C. C-linearity is built into the morphism types;
the third clause is A-linearity for the A-action induced by multiplication on M. Together
these express linearity over A tensor-over-R C. The B-action is restriction of the C-action.

Proof using the canonical flat cohomology map already defined in the models:
1. Flatness makes extension of scalars exact, so `flatHomologyMap` is the inverse
   of the canonical homology isomorphism. Composing with homology of `extendCompIso`
   proves that `baseChangeMap` is an isomorphism for every R-complex.
2. Naturality of the inverse homology isomorphism and of `extendCompIso` proves
   naturality of `baseChangeMap` for every chain map. Apply it to the resolved
   restriction of `f : M → N`; the A-action clause is the case `f = a • 𝟙 M`.
3. Apply the same naturality to both arrows of the comparison span: the R-resolution
   of the restricted A-augmentation, and the R-augmentation of the restricted
   A-resolution. The left span arrow is invertible on cohomology by `spanLeft_isIso`.
   Cancel its scalar extension, then cancel the left arrow over C. The two resulting
   composites agree by naturality for the right span arrow.
This proves the assertions for every flat B → C; the localization hypotheses are retained.
(blueprint: lem-pc-derived-tensor-flat-second-localization) -/
theorem derivedTensor_flat_second_localization
    (R A B C : Type v) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    (S : Submonoid B) [IsLocalization S C] (hflat : (algebraMap B C).Flat) (i : ℤ) :
    (∀ M : CochainComplex (ModuleCat.{v} A) ℤ,
      IsIso (baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i)) ∧
    (∀ (M N : CochainComplex (ModuleCat.{v} A) ℤ) (f : M ⟶ N),
      (ModuleCat.extendScalars (algebraMap B C)).map ((source R A B i).map f) ≫
          baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj N)) i =
        baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
          (source R A C i).map f) ∧
    (∀ (M : CochainComplex (ModuleCat.{v} A) ℤ) (a : A),
      (ModuleCat.extendScalars (algebraMap B C)).map
          ((source R A B i).map (a • 𝟙 M)) ≫
          baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i =
        baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
          (source R A C i).map (a • 𝟙 M)) ∧
    (∀ M : CochainComplex (ModuleCat.{v} A) ℤ,
      (ModuleCat.extendScalars (algebraMap B C)).map ((comparison R A B i).app M) ≫
          baseChangeMap R B C hflat ((restrict R A).obj ((resolution A).obj M)) i =
        baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
          (comparison R A C i).app M) := by
  have hnat (M N : CochainComplex (ModuleCat.{v} A) ℤ) (f : M ⟶ N) :=
    baseChangeMap_naturality R B C hflat i
      ((resolution R).map ((restrict R A).map f))
  refine ⟨?_, hnat, (fun M a ↦ hnat M M (a • 𝟙 M)), ?_⟩
  · intro M
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    dsimp only [baseChangeMap, flatHomologyMap]
    infer_instance
  · intro M
    let E := ModuleCat.extendScalars (algebraMap B C)
    let K := (restrict R A).obj ((resolution A).obj M)
    let q := (resolution R).map ((restrict R A).map ((augmentation A).app M))
    let p := (augmentation R).app K
    let lB := HomologicalComplex.homologyMap ((extend R B).map q) i
    let lC := HomologicalComplex.homologyMap ((extend R C).map q) i
    let rB := HomologicalComplex.homologyMap ((extend R B).map p) i
    let rC := HomologicalComplex.homologyMap ((extend R C).map p) i
    have := spanLeft_isIso R A B i
    have := spanLeft_isIso R A C i
    have : IsIso lB := by
      change IsIso ((Functor.whiskerRight (spanLeft R A B)
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} B) (.up ℤ) i)).app M)
      infer_instance
    have : IsIso lC := by
      change IsIso ((Functor.whiskerRight (spanLeft R A C)
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} C) (.up ℤ) i)).app M)
      infer_instance
    simp only [comparison, NatTrans.comp_app, NatIso.isIso_inv_app]
    change E.map (inv lB ≫ rB) ≫ baseChangeMap R B C hflat K i =
      baseChangeMap R B C hflat ((resolution R).obj ((restrict R A).obj M)) i ≫
        (inv lC ≫ rC)
    apply (cancel_epi (E.map lB)).1
    have hl := baseChangeMap_naturality R B C hflat i q
    have hr := baseChangeMap_naturality R B C hflat i p
    change E.map lB ≫ _ = baseChangeMap R B C hflat ((resolution R).obj K) i ≫ lC at hl
    change E.map rB ≫ _ = baseChangeMap R B C hflat ((resolution R).obj K) i ≫ rC at hr
    dsimp only [Functor.id_obj] at hl hr
    rw [Functor.map_comp]
    simp only [← Category.assoc, ← Functor.map_comp,
      IsIso.hom_inv_id, Category.id_comp]
    rw [hl]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hr

end RingTensorCohomology
