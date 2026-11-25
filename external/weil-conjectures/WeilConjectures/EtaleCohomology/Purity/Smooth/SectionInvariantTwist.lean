/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Identity

/-!
# The section invariant from the purity of a section

Let `g : V ⟶ B` be smooth of pure relative dimension `c`, with a closed section `s : B ⟶ V`.
The section invariant `𝒞(g, s) = Ls^* ω_g` (blueprint `lemma-section-normal-bundle--1`) is
determined by the purity of the section: an isomorphism `Rs^!(Λ_V(c)[2c]) ≅ Λ_B` yields
`𝒞(g, s) ≅ Λ_B(c)[2c]`.

The dualizing complex `ω_g` is ⊗-invertible (cohomological smoothness), so by the co-projection
formula for `Rs^!` (blueprint `lem-pur-coprojection`)

`Rs^!(Λ_V(c)[2c]) ⊗ Ls^* ω_g ≅ Rs^!(Λ_V(c)[2c] ⊗ ω_g) ≅ Rs^!(ω_g ⊗ Λ_V(c)[2c])
  ≅ Rs^! ω_g ⊗ Ls^*(Λ_V(c)[2c])`,

and `Rs^! ω_g = Rs^! Rg^! Λ_B ≅ R(s ≫ g)^! Λ_B = R(𝟙 B)^! Λ_B ≅ Λ_B`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_iso`: purity of the
  section determines the section invariant, `𝒞(g, s) ≅ Λ_B(c)[2c]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The exceptional inverse images along two equal morphisms are isomorphic; this transports
`Rf^!` along an equation `f = f'` without having to rewrite the instance arguments. -/
theorem nonempty_rightDerivedUpperShriek_iso_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    Nonempty (R(f)^![Λ] ≅ R(f')^![Λ]) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- For a section `s` of `g`, `Rs^! ω_g ≅ Λ_B`: `Rs^! Rg^! ≅ R(s ≫ g)^! = R(𝟙 B)^! ≅ 𝟭`. -/
theorem nonempty_rightDerivedUpperShriek_dualizingComplex_iso_of_comp_eq_id {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) [HasCompactification s]
    (hs : s ≫ g = 𝟙 B) :
    Nonempty ((R(s)^![Λ]).obj (dualizingComplex Λ g) ≅ constantComplex Λ B) := by
  have : HasCompactification (s ≫ g) := by rw [hs]; infer_instance
  have : QuasiCompact (s ≫ g) := by rw [hs]; infer_instance
  obtain ⟨eComp⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ s g
  obtain ⟨eId⟩ := nonempty_rightDerivedUpperShriek_iso_of_eq Λ hs
  exact ⟨(eComp.app (𝟙_ _)).symm ≪≫ eId.app _ ≪≫ (rightDerivedUpperShriekIdIso Λ B).app _⟩

variable [HasTateTwist Λ]

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

For `g : V ⟶ B` smooth of pure relative dimension `c` with a closed section `s`, purity of
the section `Rs^!(Λ_V(c)[2c]) ≅ Λ_B` determines the section invariant:
`𝒞(g, s) = Ls^* ω_g ≅ Λ_B(c)[2c]`.

The dualizing complex `ω_g` is invertible (`proposition-exceptional-inverse-image-smooth-morphism`),
and so is `Λ_V(c)[2c]`; the co-projection formula for `Rs^!` (`lem-pur-coprojection`) moves either
factor of `Λ_V(c)[2c] ⊗ ω_g` out of `Rs^!`, and `Rs^! ω_g ≅ Λ_B` since `s ≫ g = 𝟙 B`. -/
theorem nonempty_iso_sectionInvariant_twistShift_of_iso {V B : Scheme.{u}} {c : ℕ}
    (g : V ⟶ B) [SmoothOfRelativeDimension c g] [HasCompactification g] (s : B ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) [HasInvertibleExponent Λ V]
    (θ : (R(s)^![Λ]).obj ((tateObject Λ V c)⟦2 * (c : ℤ)⟧) ≅ constantComplex Λ B) :
    Nonempty (sectionInvariant Λ g s ≅ (twistShift Λ B c).obj (constantComplex Λ B)) := by
  have : HasInvertibleExponent Λ B := .of_hom s
  let ω := dualizingComplex Λ g
  let T := (tateObject Λ V c)⟦2 * (c : ℤ)⟧
  let tensV := derivedTensor (ModuleCat.{u + 1} Λ) V
  let tensB := derivedTensor (ModuleCat.{u + 1} Λ) B
  obtain ⟨Mω, ⟨eω⟩, ⟨eω'⟩⟩ := isInvertible_dualizingComplex Λ (d := c) g
  obtain ⟨MT, ⟨eT⟩, ⟨eT'⟩⟩ := (isInvertible_tateObject Λ V c).shift (2 * (c : ℤ))
  obtain ⟨flip⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) V
  obtain ⟨eS⟩ := nonempty_rightDerivedUpperShriek_dualizingComplex_iso_of_comp_eq_id Λ g s hs
  -- `Rs^!(T ⊗ ω) ≅ Rs^! T ⊗ Ls^* ω`
  let cop₁ := derivedTensorRightCompRightDerivedUpperShriekIso Λ s ω Mω eω' eω
  -- `Rs^!(ω ⊗ T) ≅ Rs^! ω ⊗ Ls^* T`
  let cop₂ := derivedTensorRightCompRightDerivedUpperShriekIso Λ s T MT eT' eT
  exact ⟨(derivedTensorLeftUnitor _ B _).symm ≪≫ (tensB.mapIso θ.symm).app _ ≪≫
    (cop₁.app T).symm ≪≫ (R(s)^![Λ]).mapIso ((flip.app T).app ω) ≪≫ cop₂.app ω ≪≫
    (tensB.mapIso eS).app _ ≪≫ (tensB.obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ s c) ≪≫
    derivedTensorLeftUnitor _ B _ ≪≫ (twistShiftConstantComplexIso Λ B c).symm⟩

end Etale

end AlgebraicGeometry
