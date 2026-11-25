/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalComparison
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelComparison

/-!
# Finite type of kernels of finite free surjections

Source: Stacks Project, Modules, Lemma 01BP(1)
(blueprint: lem-weil-pbc-finite-presentation-kernel-surjection-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- If a module has a local finite presentation, the kernel of a finite free
surjection onto it is locally of finite type.
Source: Stacks Project, Modules, Lemma 01BP(1)
(blueprint: lem-weil-pbc-finite-presentation-kernel-surjection-finite-type).

Proof:
1. For each point, `finitePresentation_local_comparison` supplies a neighborhood,
   a finite presentation, comparison maps in both directions, and an isomorphism
   between the restricted kernel and the kernel of the local finite free map.
2. `finitePresentation_kernel_comparison_generators` constructs a split epimorphism
   from the coproduct of the presentation kernel and the rank-r free module onto
   the local kernel. The finite relation generators and free basis give finite
   generating sections, which are transported along the kernel isomorphism.
3. The chosen neighborhoods cover X because each contains its indexing point.
   Assemble their finite generating sections into `LocalGeneratorsData` and apply
   `SheafOfModules.IsFiniteType.mk`. -/
theorem finitePresentation_kernel_surjection_finiteType
    (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    [F.IsFinitePresentation]
    (r : ℕ)
    (ψ : SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r)) ⟶ F)
    (hψ : Epi ψ) :
    (kernel ψ).IsFiniteType := by
  classical
  choose U hx ψ' P hP α β hα hβ he using
    finitePresentation_local_comparison X F r ψ hψ
  have hgen (x : X) : ∃ G : ((kernel ψ).over (U x)).GeneratingSections,
      G.IsFiniteType := by
    let := hP x
    obtain ⟨G, hG⟩ := finitePresentation_kernel_comparison_generators
      X (U x) (F.over (U x)) (P x) r (ψ' x) (α x) (β x) (hα x) (hβ x)
    let := hG
    exact ⟨G.ofEpi (he x).some.inv, inferInstance⟩
  choose G hG using hgen
  let σ : (kernel ψ).LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr (by
        apply eq_top_iff.mpr
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hx x⟩)
      generators := G }
  have hσ : σ.IsFiniteType := by
    constructor
    intro x
    exact hG x
  apply SheafOfModules.IsFiniteType.mk
  exact ⟨σ, hσ⟩

end AlgebraicGeometry.RingedSpace
