/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.Embedding.RestrictionExtend
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Quasi-isomorphisms of complexes of modules from sections

A morphism of complexes of `𝒪_X`-modules is a quasi-isomorphism as soon as every point has
arbitrarily small open neighbourhoods over which it is a quasi-isomorphism on sections
(`AlgebraicGeometry.Scheme.Modules.quasiIso_of_quasiIso_sectionsAb` for complexes indexed by `ℤ`,
`AlgebraicGeometry.Scheme.Modules.quasiIso_of_quasiIso_sectionsAb_nat` for complexes indexed by
`ℕ`): its mapping cone is then exact on these sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Quasi-isomorphisms from sections**, for complexes indexed by `ℤ`. -/
theorem quasiIso_of_quasiIso_sectionsAb {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      QuasiIso (((sectionsAb W).mapHomologicalComplex _).map φ)) : QuasiIso φ := by
  rw [CochainComplex.mappingCone.quasiIso_iff_acyclic]
  intro n
  refine exactAt_of_exactAt_sectionsAb _ n fun x V hx ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hx
  refine ⟨W, hxW, hWV, ?_⟩
  exact ((CochainComplex.mappingCone.quasiIso_iff_acyclic _).1 hW n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ (sectionsAb W)).symm

/-- **Quasi-isomorphisms from sections**, for complexes indexed by `ℕ`. -/
theorem quasiIso_of_quasiIso_sectionsAb_nat {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L)
    (h : ∀ (x : X) (V : X.Opens), x ∈ V → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      QuasiIso (((sectionsAb W).mapHomologicalComplex _).map φ)) : QuasiIso φ := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff φ ComplexShape.embeddingUpNat]
  refine quasiIso_of_quasiIso_sectionsAb _ fun x V hx ↦ ?_
  obtain ⟨W, hxW, hWV, hW⟩ := h x V hx
  refine ⟨W, hxW, hWV, ?_⟩
  have hsq : ((sectionsAb W).mapHomologicalComplex _).map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat (sectionsAb W)).hom =
      (K.mapExtendIso ComplexShape.embeddingUpNat (sectionsAb W)).hom ≫
        HomologicalComplex.extendMap (((sectionsAb W).mapHomologicalComplex _).map φ)
          ComplexShape.embeddingUpNat := by
    ext i : 1
    exact HomologicalComplex.mapExtensIso_hom_f_naturality φ _ (sectionsAb W) i
  rw [← quasiIso_iff_comp_right _ (L.mapExtendIso ComplexShape.embeddingUpNat (sectionsAb W)).hom,
    hsq, quasiIso_iff_comp_left, HomologicalComplex.quasiIso_extendMap_iff]
  exact hW

end AlgebraicGeometry.Scheme.Modules
