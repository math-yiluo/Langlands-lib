/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!
# Multiplication by a nonzerodivisor on an injective sheaf of modules is an epimorphism

Let `Λ` be a commutative ring, `ϖ ∈ Λ` a nonzerodivisor and `I` an injective sheaf of
`Λ`-modules on a site. Multiplication by `ϖ` on `I` is an epimorphism: a section `s` of `I` over
`U` is a morphism from the sheafified free `Λ`-module sheaf on `U`, on which multiplication by `ϖ`
is a monomorphism, and extending along it divides `s` by `ϖ`. This is the module version of
`CategoryTheory.Sheaf.epi_nsmul_id_of_injective`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type (max w v)} [CommRing Λ] [HasSheafify J (ModuleCat.{max w v} Λ)]

variable (Λ) in
/-- The free presheaf of `Λ`-modules on `U`. -/
noncomputable abbrev freeModuleYoneda (U : C) : Cᵒᵖ ⥤ ModuleCat.{max w v} Λ :=
  uliftYoneda.{w}.obj U ⋙ ModuleCat.free Λ

/-- The morphism from the free presheaf of `Λ`-modules on `U` to `F` determined by a section of
`F` over `U`. -/
noncomputable def freeModuleYonedaHom (U : C) (F : Cᵒᵖ ⥤ ModuleCat.{max w v} Λ)
    (s : F.obj (op U)) : freeModuleYoneda.{w} Λ U ⟶ F where
  app V := ModuleCat.ofHom (Finsupp.linearCombination Λ fun g ↦ F.map g.down.op s)
  naturality V W g := by
    ext x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [ModuleCat.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
    | single a r =>
      change Finsupp.linearCombination Λ _ (Finsupp.mapDomain _ (Finsupp.single a r)) =
        F.map g (Finsupp.linearCombination Λ _ (Finsupp.single a r))
      rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, map_smul]
      congr 1
      change (F.map ((g.unop ≫ a.down).op)) s = _
      rw [op_comp, F.map_comp]
      rfl

/-- The generator of the free presheaf of `Λ`-modules on `U` over `U`: the identity of `U`. -/
noncomputable def freeModuleYonedaGen (U : C) : (freeModuleYoneda.{w} Λ U).obj (op U) :=
  Finsupp.single (ULift.up (𝟙 U)) 1

lemma freeModuleYonedaHom_gen (U : C) (F : Cᵒᵖ ⥤ ModuleCat.{max w v} Λ) (s : F.obj (op U)) :
    (freeModuleYonedaHom.{w} U F s).app (op U) (freeModuleYonedaGen.{w} U) = s := by
  change Finsupp.linearCombination Λ _ (Finsupp.single _ 1) = s
  rw [Finsupp.linearCombination_single, one_smul]
  simp

/-- Multiplication by a nonzerodivisor on the free presheaf of `Λ`-modules on `U` is a
monomorphism. -/
lemma mono_smul_id_freeModuleYoneda (U : C) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) :
    Mono (ϖ • 𝟙 (freeModuleYoneda.{w} Λ U)) := by
  have (V : Cᵒᵖ) : Mono ((ϖ • 𝟙 (freeModuleYoneda.{w} Λ U)).app V) := by
    rw [ModuleCat.mono_iff_injective]
    intro (x : _ →₀ Λ) (y : _ →₀ Λ) (hxy : ϖ • x = ϖ • y)
    refine Finsupp.ext fun a ↦ ?_
    have := congrArg (fun z ↦ z a) hxy
    simp only [Finsupp.smul_apply, smul_eq_mul] at this
    rw [← sub_eq_zero, ← mul_sub] at this
    rw [← sub_eq_zero]
    exact (mem_nonZeroDivisors_iff.1 hϖ).2 _ (by rw [mul_comm]; exact this)
  exact NatTrans.mono_of_mono_app _

variable [J.HasSheafCompose (forget (ModuleCat.{max w v} Λ))]

/-- **Injective sheaves of modules are `ϖ`-divisible.** Multiplication by a nonzerodivisor `ϖ`
on an injective sheaf of `Λ`-modules is an epimorphism. -/
theorem epi_smul_id_of_injective (I : Sheaf J (ModuleCat.{max w v} Λ)) [Injective I] {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) : Epi (ϖ • 𝟙 I) := by
  let P (U : C) : Sheaf J (ModuleCat.{max w v} Λ) :=
    (presheafToSheaf J _).obj (freeModuleYoneda.{w} Λ U)
  have hP (U : C) : Mono (ϖ • 𝟙 (P U)) := by
    have := mono_smul_id_freeModuleYoneda.{w} U hϖ
    rw [← Functor.map_id, ← Functor.map_smul]
    infer_instance
  let e (U : C) (g : P U ⟶ I) : I.obj.obj (op U) :=
    g.hom.app (op U) ((toSheafify J (freeModuleYoneda.{w} Λ U)).app (op U)
      (freeModuleYonedaGen.{w} U))
  have he (U : C) (s : I.obj.obj (op U)) :
      e U ⟨sheafifyLift J (freeModuleYonedaHom.{w} U I.obj s) I.property⟩ = s := by
    change ((toSheafify J _ ≫ (sheafifyLift J (freeModuleYonedaHom.{w} U I.obj s)
      I.property)).app (op U)) _ = s
    rw [toSheafify_sheafifyLift]
    exact freeModuleYonedaHom_gen U I.obj s
  have hsurj (U : C) : Function.Surjective ((ϖ • 𝟙 I).hom.app (op U)) := by
    intro s
    let f : P U ⟶ I := ⟨sheafifyLift J (freeModuleYonedaHom.{w} U I.obj s) I.property⟩
    let g := Injective.factorThru f (ϖ • 𝟙 (P U))
    refine ⟨e U g, ?_⟩
    have hg : (ϖ • 𝟙 (P U)) ≫ g = f := Injective.comp_factorThru f (ϖ • 𝟙 (P U))
    rw [← he U s]
    change _ = e U f
    rw [← hg, Linear.smul_comp, Category.id_comp, ← Category.comp_id g, ← Linear.comp_smul]
    rfl
  have : Sheaf.IsLocallySurjective (ϖ • 𝟙 I) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun U ↦ hsurj U.unop
  exact Sheaf.epi_of_isLocallySurjective _

end Sheaf

end CategoryTheory
