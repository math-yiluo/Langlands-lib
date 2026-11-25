/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The relative tangent bundle

For a morphism `f : X ⟶ Y`, the sheaf of relative differentials `Ω¹_{X/Y}` is quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials`), and the *relative tangent
bundle* is the vector bundle `T_{X/Y} = Spec_X Sym_{𝒪_X}(Ω¹_{X/Y})`
(`AlgebraicGeometry.Scheme.Modules.symSpec`), with its zero section `X ⟶ T_{X/Y}`
corresponding to the augmentation `Sym_{𝒪_X}(Ω¹_{X/Y}) ⟶ 𝒪_X`, which kills `Ω¹_{X/Y}`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.tangentBundle`: the relative tangent bundle `T_{X/Y}`, with its
  projection `tangentBundleProj` and its zero section `tangentBundleZeroSection`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.tangentBundleZeroSection_tangentBundleProj`: the zero section is
  a section of the projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every point of `X` has an affine open neighbourhood `V` mapping into an affine open `U` of
`Y`. -/
lemma exists_isAffineOpen_le_preimage (x : X) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      V ≤ f ⁻¹ᵁ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).isOpen
  exact ⟨U, hU, V, hV, hxV, hVU⟩

/-- The sheaf of relative differentials `Ω¹_{X/Y}` is quasi-coherent: on an affine open
`V = Spec B` of `X` mapping into an affine open `Spec A` of `Y` it is `Ω_{B/A}^~`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsRestrictFromSpecIso`). -/
instance isQuasicoherent_relativeDifferentials : f.relativeDifferentials.IsQuasicoherent := by
  choose U hU V hV hxV hVU using f.exists_isAffineOpen_le_preimage
  refine Modules.isQuasicoherent_of_iSup_opensRange_eq_top _ (fun x ↦ (hV x).fromSpec)
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2
      ⟨x, by rw [IsAffineOpen.opensRange_fromSpec]; exact hxV x⟩) fun x ↦ ?_
  exact (presentationTilde _ Set.univ (by simp) _ (Submodule.span_eq _)).ofIsIso
    (f.relativeDifferentialsRestrictFromSpecIso (hU x) (hV x) (hVU x)).inv

/-- Blueprint `prose-09-15`: Relative tangent bundle

The relative tangent bundle `T_{X/Y} = Spec_X Sym_{𝒪_X}(Ω¹_{X/Y})` of a morphism `f : X ⟶ Y`.
The blueprint considers it for smooth `f`, where `Ω¹_{X/Y}` is locally free
(`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials`), but the
construction makes sense for every morphism. -/
noncomputable def tangentBundle : Scheme.{u} :=
  f.relativeDifferentials.symSpec

/-- Blueprint `prose-09-15`: Relative tangent bundle

The projection `T_{X/Y} ⟶ X`. -/
noncomputable def tangentBundleProj : f.tangentBundle ⟶ X :=
  f.relativeDifferentials.symSpecProj

/-- Blueprint `prose-09-15`: Relative tangent bundle

The zero section `X ⟶ T_{X/Y}`, corresponding to the augmentation
`Sym_{𝒪_X}(Ω¹_{X/Y}) ⟶ 𝒪_X`. -/
noncomputable def tangentBundleZeroSection : X ⟶ f.tangentBundle :=
  f.relativeDifferentials.symSpecZeroSection

/-- The zero section of the relative tangent bundle is a section of its projection. -/
@[reassoc (attr := simp)]
lemma tangentBundleZeroSection_tangentBundleProj :
    f.tangentBundleZeroSection ≫ f.tangentBundleProj = 𝟙 X :=
  f.relativeDifferentials.symSpecZeroSection_symSpecProj

end Scheme.Hom

end AlgebraicGeometry
