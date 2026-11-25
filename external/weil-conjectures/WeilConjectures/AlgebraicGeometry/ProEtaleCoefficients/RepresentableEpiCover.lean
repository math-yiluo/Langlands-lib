/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-! Representable epimorphisms are singleton covers under the qcqs hypotheses.

## References

* Stacks Project, Tag 00WN and pro-etale covering definition Tag 098K
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

set_option backward.isDefEq.respectTransparency false in
/-- A represented epimorphism with quasi-compact source and quasi-separated target covers. -/
theorem singleton_cover_of_representable_epi (X : Scheme.{u}) {A B : X.ProEt}
    (μ : A ⟶ B) [CompactSpace A.left] [QuasiSeparatedSpace B.left]
    (hμ : Epi ((topology X).yoneda.map μ)) :
    Presieve.singleton μ ∈ precoverage X B := by
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderComposition := by
    dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by
    dsimp [precoverage]; infer_instance
  have : (precoverage X).HasPullbacks := by dsimp [precoverage]; infer_instance
  obtain ⟨S, hS, hlift⟩ := representable_epi_local_lifting X μ hμ B (𝟙 B)
  obtain ⟨R, hR, hRS⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  have hR' : R.map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage B.left := hR
  have hsurj : Surjective μ.left := by
    constructor
    intro y
    obtain ⟨Y, f, hf, x, hx⟩ := hR'.2.1 y
    rcases hf with @⟨C, g, hg⟩
    rcases hg with @⟨V, f, hf⟩
    obtain ⟨t, ht⟩ := hlift V f (hRS _ _ hf)
    refine ⟨t.left x, ?_⟩
    have he : t.left ≫ μ.left = f.left := by
      have h := congrArg (fun k ↦ (ProEt.forget X ⋙ Over.forget X).map k) ht
      simp only [Functor.map_comp, Category.comp_id] at h
      change t.left ≫ μ.left = f.left at h
      exact h
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k x) he |>.trans hx
  let := hsurj
  have : QuasiCompact μ.left := inferInstance
  have hw : WeaklyEtale μ.left := by
    have : WeaklyEtale (μ.left ≫ B.hom) := by
      rw [MorphismProperty.Over.w μ]
      infer_instance
    exact WeaklyEtale.of_comp μ.left B.hom
  change (Presieve.singleton μ).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
    Scheme.proetalePrecoverage B.left
  rw [Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_propQCPrecoverage (f := μ.left) hw

end AlgebraicGeometry.Scheme.ProEt
