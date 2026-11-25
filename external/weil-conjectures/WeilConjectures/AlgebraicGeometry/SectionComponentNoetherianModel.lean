/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.SectionNoetherianDescent

/-!
# Local noetherian models for the component selected by a section

Source: Stacks Project, Tag 055P, first reduction, and Tag 055M.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Near each source point, the section component is the inverse image of the section
component of a finitely presented morphism between noetherian schemes.

Source: Stacks Project, Tag 055P, first reduction, using Tags 01ZM and 055M.
Proof: choose an affine neighbourhood V of g(p) and put U = g inverse image V.
The restriction of g to U is finitely presented, since g is locally finitely presented,
quasi-compact and quasi-separated. Write the coordinate ring of V as the filtered union
of its finitely generated Z-subalgebras. Finite-presentation descent (01ZM) descends the
restricted morphism, its section and the section identity to a finite stage. Let T0 be
that affine stage and P0 its finitely presented source. Both are noetherian, since T0 is
of finite type over Z and P0 is of finite type over T0. The projection rho from the base
change to P0 is a scheme morphism. The section component commutes with this base change
by 055M: the connected component of the rational section point is geometrically connected,
so its base change is contained in the new component, while the continuous image of the
new component is connected and contains the original section point, giving the reverse
inclusion. Restriction to V does not change the fibres or their section points. This
identifies the original component on U with the displayed inverse image.

(blueprint: lem-sbc-section-component-noetherian-model) -/
theorem exists_section_component_noetherian_model {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (p : P) :
    ∃ (U : P.Opens), p ∈ U ∧ ∃ (P₀ T₀ : Scheme.{u}) (g₀ : P₀ ⟶ T₀)
      (σ₀ : T₀ ⟶ P₀) (ρ : U.toScheme ⟶ P₀),
      IsNoetherian P₀ ∧ IsNoetherian T₀ ∧ LocallyOfFinitePresentation g₀ ∧
      QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧ σ₀ ≫ g₀ = 𝟙 T₀ ∧
      U.ι ⁻¹' {q : P | q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q))} =
        ρ ⁻¹' {q : P₀ | q ∈ connectedComponentIn (g₀ ⁻¹' {g₀ q}) (σ₀ (g₀ q))} := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, _⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g p)) isOpen_univ
  let V : T.Opens := V
  let : IsAffine V.toScheme := hV
  let U := g ⁻¹ᵁ V
  let f := g ∣_ V
  have H : IsPullback U.ι f g V.ι := (isPullback_morphismRestrict g V).flip
  let σV : V.toScheme ⟶ U.toScheme := H.lift (V.ι ≫ σ) (𝟙 V.toScheme) (by
    simp [hσ])
  have hσV : σV ≫ f = 𝟙 V.toScheme := H.lift_snd _ _ _
  have hcompat : σV ≫ U.ι = V.ι ≫ σ := H.lift_fst _ _ _
  obtain ⟨P₀, T₀, g₀, σ₀, ρ, b, hP₀, hT₀, hg₀, hqc₀, hqs₀, hσ₀, H₀, hcompat₀⟩ :=
    exists_noetherian_model_with_section f σV hσV
  let : LocallyOfFinitePresentation g₀ := hg₀
  refine ⟨U, hpV, P₀, T₀, g₀, σ₀, ρ, hP₀, hT₀, hg₀, hqc₀, hqs₀, hσ₀, ?_⟩
  exact (section_component_preimage_of_isPullback g σ hσ U.ι f V.ι H σV hσV hcompat).trans
    (section_component_preimage_of_isPullback g₀ σ₀ hσ₀ ρ f b H₀ σV hσV hcompat₀).symm

end AlgebraicGeometry
