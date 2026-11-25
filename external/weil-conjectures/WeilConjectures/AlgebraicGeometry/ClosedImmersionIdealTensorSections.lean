/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Sections vanishing along a closed immersion -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring the ideal inclusion by an invertible tensor power identifies its sections
with the kernel of restriction to the closed subscheme.

Source: Stacks Project, Modules Lemma 08KS and Varieties Lemma 09NX, extension by zero.
(blueprint: lem-sc-closed-immersion-ideal-tensor-sections).

Proof: an invertible module and every tensor power are locally free of rank one.
Tensoring the ideal inclusion is therefore a monomorphism. The closed-immersion unit
quotient theorem identifies the image of ideal multiplication with the kernel of the
pullback unit. This remains true for the canonical adjunction: comparing two adjunctions
of the same functors changes the unit by an automorphism of the target, which preserves
its kernel. Evaluation on an open preserves kernels, so on the top open the multiplication
map is injective and its range is exactly the sections killed by restriction. This also
covers an empty closed subscheme, where the ideal is the whole structure module, and
power zero, where the module is the structure module. -/
theorem closedImmersion_ideal_tensor_sections {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsClosedImmersion j] (M : Y.Modules) [M.IsInvertible] (m : ℕ) :
    let N := M.tensorPow m
    let adjZ := Classical.choose (exists_tensorPullbackAdjunction j)
    let resZ : Γ(N, ⊤) → Γ((tensorPullback j).obj N, ⊤) :=
      fun t ↦ (adjZ.unit.app N).val.app (op ⊤) t
    let μ : j.ker.toModules ⊗ N ⟶ N := j.ker.toModulesι ▷ N ≫ (λ_ N).hom
    Function.Injective (μ.app ⊤) ∧
      ∀ t : Γ(N, ⊤), resZ t = 0 ↔ ∃ s, μ.app ⊤ s = t  := by
  classical
  dsimp only
  let N := M.tensorPow m
  let μ : j.ker.toModules ⊗ N ⟶ N := j.ker.toModulesι ▷ N ≫ (λ_ N).hom
  have : Mono μ := inferInstance
  let adj₀ := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  let η₀ := adj₀.unit.app N
  let η := adj.unit.app N
  obtain ⟨η', hη', _⟩ := closedImmersion_unit_quotient j
  obtain ⟨_, ⟨w, ⟨hlim⟩⟩, _, _⟩ := hη' N
  let e₀ : image μ ≅ kernel η₀ :=
    hlim.conePointUniqueUpToIso (limit.isLimit _)
  have he₀ : e₀.hom ≫ kernel.ι η₀ = image.ι μ :=
    hlim.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  let e : j.ker.toModules ⊗ N ≅ kernel η₀ := (imageMonoIsoSource μ).symm ≪≫ e₀
  have he : e.hom ≫ kernel.ι η₀ = μ := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, he₀]
    exact imageMonoIsoSource_inv_ι μ
  have hinj : Function.Injective (μ.app ⊤) :=
    (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map μ)).mp inferInstance
  refine ⟨hinj, ?_⟩
  intro t
  have hunit := Adjunction.unit_rightAdjointUniq_hom_app adj₀ adj N
  let d := (Adjunction.rightAdjointUniq adj₀ adj).app ((tensorPullback j).obj N)
  have hd : η₀ ≫ d.hom = η := hunit
  have hk : η.app ⊤ t = 0 ↔ η₀.app ⊤ t = 0 := by
    have hdapp : Function.Injective (d.hom.app ⊤) :=
      (ModuleCat.mono_iff_injective
        ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map d.hom)).mp inferInstance
    constructor
    · intro ht
      apply hdapp
      calc
        d.hom.app ⊤ (η₀.app ⊤ t) = η.app ⊤ t := by
          exact congrArg (fun f ↦ f.app ⊤ t) hd
        _ = 0 := ht
        _ = d.hom.app ⊤ 0 := (map_zero _).symm
    · intro ht
      calc
        η.app ⊤ t = d.hom.app ⊤ (η₀.app ⊤ t) := by
          exact (congrArg (fun f ↦ f.app ⊤ t) hd).symm
        _ = 0 := by rw [ht, map_zero]
  change η.app ⊤ t = 0 ↔ ∃ s, μ.app ⊤ s = t
  rw [hk]
  have hrange := range_map_kernelι (X := Y) ⊤ η₀
  constructor
  · intro ht
    obtain ⟨z, hz⟩ := (Set.ext_iff.mp hrange t).2 ht
    refine ⟨e.inv.app ⊤ z, ?_⟩
    have hei : e.inv ≫ μ = kernel.ι η₀ := by
      rw [← he, Iso.inv_hom_id_assoc]
    exact (congrArg (fun f ↦ f.app ⊤ z) hei).trans hz
  · rintro ⟨s, rfl⟩
    have hcondition : μ ≫ η₀ = 0 := by rw [← he, Category.assoc, kernel.condition, comp_zero]
    exact congrArg (fun f ↦ f.app ⊤ s) hcondition


end AlgebraicGeometry.Scheme.Modules
