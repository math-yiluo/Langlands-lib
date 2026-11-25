/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionEtaleChart
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantTwist
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClassField
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomFramesFundamentalClass

/-!
# Purity for a section of a smooth morphism

Let `g : V ⟶ B` be smooth of relative dimension `c`, with a closed section `s : B ⟶ V`, over a
base `B` separated and locally of finite type over a field. Near every point of `s(B)` there are
étale coordinates `x₁, …, x_c` on `V` over `B` cutting out the section
(`AlgebraicGeometry.exists_etale_affineSpace_of_section`). They form a Zariski frame of `s` given
by a weakly regular sequence, and its class `∂κ(x₁) ∪ ⋯ ∪ ∂κ(x_c)` is the restriction along the
étale chart `V ⊇ U ⟶ 𝔸^c_W` of the Thom class of the zero section of `𝔸^c_W`, whose adjoint is
an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field`).
So `s` has Thom frames and regular Zariski frames, the frame classes glue to a fundamental class,
and `Rs^! (Λ_V(c)[2c]) ≅ Λ_B`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_tateObject_of_hasThomFrames`).
By the co-projection formula this computes the section invariant, `𝒞(g, s) ≅ Λ_B(c)[2c]`
(`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_iso`).

Applied to the diagonal of a smooth morphism, a section of the first projection, this is
smooth purity (`proposition-smooth-purity-finite-coefficients`,
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`).

## Main statements

- `AlgebraicGeometry.Etale.hasThomFrames_of_section`,
  `AlgebraicGeometry.Etale.hasRegularZariskiFrames_of_section`: the coordinate frames.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_tateObject_of_section`:
  `Rs^! (Λ_V(c)[2c]) ≅ Λ_B`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_section`:
  `𝒞(g, s) ≅ Λ_B(c)[2c]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} (c : ℕ) (g : V ⟶ B)
  [SmoothOfRelativeDimension c g] (s : B ⟶ V) [IsClosedImmersion s]

/-- **The coordinate frames of a section are Thom frames.** Every point of `B` lies in the zero
locus of a Zariski frame of `s` given by étale coordinates `x₁, …, x_c` on an affine open
`U ⊆ V`, and the adjoint of its class is an isomorphism: the class is the restriction, along the
étale chart `U ⟶ 𝔸^c_W`, of the Thom class of the zero section of `𝔸^c_W`, with `W ⊆ B` affine
and hence separated and locally of finite type over the field. -/
theorem hasThomFrames_of_section [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]
    (hs : s ≫ g = 𝟙 B) {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [HasInvertibleExponent Λ V] :
    HasThomFrames Λ c s := by
  intro b
  obtain ⟨W, -, U, hbU, f, v, hf, -, hv, hvf, -⟩ :=
    exists_etale_affineSpace_of_section c g s hs b
  refine ⟨Scheme.Hom.EtaleFrame.ofSpanEq s U f hf,
    Scheme.Hom.EtaleFrame.mem_range_ofSpanEq_toZ s U f hf hbU, ?_⟩
  have : HasInvertibleExponent Λ B := .of_hom s
  have : HasInvertibleExponent Λ W.toScheme := .of_hom W.ι
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); W.toScheme) :=
    .of_hom (𝔸(ULift.{u} (Fin c); W.toScheme) ↘ W.toScheme)
  have : HasInvertibleExponent Λ U.1.toScheme := .of_hom U.1.ι
  exact isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ v _ _ hvf
    (isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field Λ c W.toScheme (W.ι ≫ aB))

/-- **The coordinate frames of a section are regular.** Every point of `B` lies in the zero
locus of a Zariski frame of `s` on an affine open of `V`, given by étale coordinates
`x₁, …, x_c`, which form a weakly regular sequence. -/
theorem hasRegularZariskiFrames_of_section (hs : s ≫ g = 𝟙 B) :
    HasRegularZariskiFrames c s := by
  intro b
  obtain ⟨W, -, U, hbU, f, v, hf, hreg, -⟩ := exists_etale_affineSpace_of_section c g s hs b
  refine ⟨Scheme.Hom.EtaleFrame.ofSpanEq s U f hf, inferInstance,
    Scheme.Hom.EtaleFrame.mem_range_ofSpanEq_toZ s U f hf hbU, inferInstance, ?_⟩
  have hf' : List.ofFn (Scheme.Hom.EtaleFrame.ofSpanEq s U f hf).f =
      (List.ofFn f).map U.1.topIso.inv.hom := by
    rw [List.map_ofFn]
    rfl
  rw [hf']
  exact hreg.map_of_flat (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso U.1.topIso.inv))

/-- **Purity for a section of a smooth morphism.** For `g : V ⟶ B` smooth of relative dimension
`c` with a closed section `s`, `B` separated and locally of finite type over a field,
`Rs^! (Λ_V(c)[2c]) ≅ Λ_B`: the inverse of the adjoint of the fundamental class of `s`, glued
from the classes of the coordinate frames. -/
theorem nonempty_iso_rightDerivedUpperShriek_tateObject_of_section [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] (hs : s ≫ g = 𝟙 B) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ V] :
    Nonempty ((R(s)^![Λ]).obj ((tateObject Λ V c)⟦2 * (c : ℤ)⟧) ≅ constantComplex Λ B) :=
  have := SmoothOfRelativeDimension.smooth c g
  nonempty_iso_rightDerivedUpperShriek_tateObject_of_hasThomFrames Λ
    (hasThomFrames_of_section Λ c g s hs aB) (hasRegularZariskiFrames_of_section c g s hs)
    (g ≫ aB)

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

**The section invariant of a section of a smooth morphism.** For `g : V ⟶ B` smooth of relative
dimension `c` with a closed section `s`, `B` separated and locally of finite type over a field,
and a normalized Tate twist,

`𝒞(g, s) = Ls^* ω_g ≅ Λ_B(c)[2c]`.

The twist underlies a normalized rank-one datum, for which `Rs^! (Λ_V(c)[2c]) ≅ Λ_B`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_tateObject_of_section`), and this
determines the section invariant
(`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_iso`). -/
theorem nonempty_iso_sectionInvariant_twistShift_of_section [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] [HasCompactification g] (hs : s ≫ g = 𝟙 B) {k : Type u}
    [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ V] :
    Nonempty (sectionInvariant Λ g s ≅ (twistShift Λ B c).obj (constantComplex Λ B)) := by
  obtain ⟨K, hK, hN⟩ := HasTateTwist.IsNormalized.exists_hasKummerClass (Λ := Λ)
  subst hK
  obtain ⟨θ⟩ := nonempty_iso_rightDerivedUpperShriek_tateObject_of_section Λ c g s hs aB
  exact nonempty_iso_sectionInvariant_twistShift_of_iso Λ g s hs θ

end Etale

end AlgebraicGeometry
