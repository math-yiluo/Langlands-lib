/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentNoetherianModel
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentNoetherianGeneralization

/-!
# Generalization stability of a smooth section component

Source: Stacks Project, Tag 055Q, generic-point argument.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The relative connected component of a smooth section is stable under generalization.

Source: Stacks Project, Tag 055Q, specifically its generic-point argument.
Proof: smoothness supplies flatness and geometrically reduced fibres. Work locally on the
base and descend the finite-presentation morphism and section to a noetherian model,
retaining flatness. The component containing the rational section point commutes with
base change by Tag 055M. For a specialization from x' to x with x in the section component,
choose a trait mapping its generic and special points to x' and x. After base change,
remove the other special-fibre components. The remaining special fibre is connected.
Restrict further to the connected component of the total space containing the section;
it contains the whole special fibre. Tag 055J makes its generic fibre connected, since
the family is flat and the special fibre is geometrically reduced. The trait's second
section through x and x' consequently has its generic point in the component selected
by the original section. Its image x' is in the required locus. Base-change compatibility
returns the conclusion on the original scheme.

(blueprint: lem-sbc-smooth-section-component-generalization) -/
theorem Smooth.stableUnderGeneralization_section_component {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    StableUnderGeneralization
      {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  intro x y hxy hx
  obtain ⟨W, hxW, P₀, T₀, g₀, σ₀, a, hT₀, hg₀, hqc, hqs, hσ₀, hcomp⟩ :=
    Smooth.exists_section_component_noetherian_model g σ hσ x
  let : IsNoetherian T₀ := hT₀
  let : Smooth g₀ := hg₀
  let : QuasiCompact g₀ := hqc
  let : QuasiSeparated g₀ := hqs
  have hyW : y ∈ W := hxy.mem_open W.isOpen hxW
  let xW : W.toScheme := ⟨x, hxW⟩
  let yW : W.toScheme := ⟨y, hyW⟩
  have hxyW : yW ⤳ xW := (subtype_specializes_iff yW xW).mpr hxy
  have hx₀ : a xW ∈ connectedComponentIn (g₀ ⁻¹' {g₀ (a xW)}) (σ₀ (g₀ (a xW))) :=
    (hcomp xW).mp hx
  exact (hcomp yW).mpr
    (Smooth.section_component_generalization_of_isNoetherian g₀ σ₀ hσ₀
      (hxyW.map a.continuous) hx₀)

end AlgebraicGeometry
