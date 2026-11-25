/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!

# Affine charts of the affine compactification

The relative projective space `ℙ(Option n; S)` is covered by the images of open immersions
`𝔸(n; S) ⟶ ℙ(Option n; S)` over `S`: for `a : Option n`, the chart onto `D₊(T_a)` is the
standard chart `AffineSpace.toRelativeProjectiveSpace` onto `D₊(T_none)` followed by the
automorphism of `ℙ(Option n; S)` swapping the homogeneous coordinates `T_none` and `T_a`.

Consequently the compactification `Compactification.ofIsImmersionAffineSpace` of a scheme
immersed in `𝔸(n; S)`, being a closed subscheme of `ℙ(Option n; S)`, locally embeds into
`𝔸(n; S)` over `S`.

## Main definitions

- `AlgebraicGeometry.Proj.renameMap`: the morphism of projective spectra of polynomial rings
  induced by a bijection of the variables.
- `AlgebraicGeometry.ProjectiveSpace.rename`: the induced morphism of relative projective
  spaces over `S`.
- `AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpaceChart`: the chart
  `𝔸(n; S) ⟶ ℙ(Option n; S)` onto `D₊(T_a)`.

## Main results

- `AlgebraicGeometry.AffineSpace.exists_mem_range_toRelativeProjectiveSpaceChart`: the charts
  cover `ℙ(Option n; S)`.
- `AlgebraicGeometry.Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace`:
  the affine compactification locally embeds into `𝔸(n; S)` over `S`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Proj

variable {σ τ R : Type u} [CommRing R]

/-- Renaming the variables along a bijection `E : σ ≃ τ`, as a graded ring homomorphism of
polynomial rings with their total-degree gradings. -/
noncomputable def renameGradedHom (E : σ ≃ τ) :
    homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule τ R where
  __ := (renameEquiv R E).toRingHom
  map_mem h := h.rename_isHomogeneous

@[simp]
lemma renameGradedHom_apply (E : σ ≃ τ) (p : MvPolynomial σ R) :
    renameGradedHom E p = rename E p :=
  rfl

/-- Renaming the variables maps the irrelevant ideal onto the irrelevant ideal. -/
lemma irrelevant_le_map_renameGradedHom (E : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).map (renameGradedHom E) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    toIdeal_irrelevant_homogeneousSubmodule, toIdeal_irrelevant_homogeneousSubmodule,
    Ideal.map_span]
  refine Ideal.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨X (E.symm i), ⟨E.symm i, rfl⟩, by simp⟩

/-- The morphism `Proj R[τ] ⟶ Proj R[σ]` induced by renaming the variables along `E`. -/
noncomputable def renameMap (E : σ ≃ τ) :
    Proj (homogeneousSubmodule τ R) ⟶ Proj (homogeneousSubmodule σ R) :=
  Proj.map (renameGradedHom E) (irrelevant_le_map_renameGradedHom E)

@[simp]
lemma renameMap_preimage_basicOpen (E : σ ≃ τ) (s : MvPolynomial σ R) :
    renameMap E ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) s =
      Proj.basicOpen (homogeneousSubmodule τ R) (rename E s) :=
  rfl

@[reassoc (attr := simp)]
lemma renameMap_symm_comp (E : σ ≃ τ) :
    renameMap (R := R) E.symm ≫ renameMap E = 𝟙 _ := by
  rw [renameMap, renameMap, ← Proj.map_comp]
  convert Proj.map_id
  ext p
  simp

instance (E : σ ≃ τ) : IsIso (renameMap (R := R) E) :=
  ⟨renameMap E.symm, by simpa using renameMap_symm_comp (R := R) E.symm,
    renameMap_symm_comp E⟩

/-- The standard opens `D₊(Tᵢ)` cover the projective spectrum of a polynomial ring. -/
lemma iSup_basicOpen_X_eq_top :
    ⨆ i : σ, Proj.basicOpen (homogeneousSubmodule σ R) (X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (toIdeal_irrelevant_homogeneousSubmodule σ R).le

end Proj

namespace ProjectiveSpace

variable {σ τ : Type u} (S : Scheme.{u})

/-- The morphism `ℙ(τ; S) ⟶ ℙ(σ; S)` over `S` induced by renaming the homogeneous coordinates
along a bijection `E : σ ≃ τ`. -/
noncomputable def rename (E : σ ≃ τ) : ℙ(τ; S) ⟶ ℙ(σ; S) :=
  pullback.map _ _ _ _ (𝟙 S) (Proj.renameMap E) (𝟙 _) (by simp) (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma rename_over (E : σ ≃ τ) : rename S E ≫ ℙ(σ; S) ↘ S = ℙ(τ; S) ↘ S := by
  simp [rename, over_over]

@[reassoc (attr := simp)]
lemma rename_toProjInt (E : σ ≃ τ) :
    rename S E ≫ toProjInt σ S = toProjInt τ S ≫ Proj.renameMap E :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma rename_symm_comp (E : σ ≃ τ) : rename S E.symm ≫ rename S E = 𝟙 _ := by
  ext1
  · simp
  · simp only [Category.assoc, rename_toProjInt, rename_toProjInt_assoc,
      Proj.renameMap_symm_comp, Category.id_comp]
    exact Category.comp_id (toProjInt σ S)

instance (E : σ ≃ τ) : IsIso (rename S E) :=
  ⟨rename S E.symm, by simpa using rename_symm_comp S E.symm, rename_symm_comp S E⟩

end ProjectiveSpace

namespace AffineSpace

variable {n : Type u} (S : Scheme.{u})

/-- The standard affine chart `𝔸(n; S) ⟶ ℙ(Option n; S)` onto `D₊(T_a)`: the standard chart
onto `D₊(T_none)` followed by the automorphism swapping the coordinates `T_none` and `T_a`. -/
noncomputable def toRelativeProjectiveSpaceChart [DecidableEq n] (a : Option n) :
    𝔸(n; S) ⟶ ℙ(Option n; S) :=
  toRelativeProjectiveSpace n S ≫ ProjectiveSpace.rename S (Equiv.swap none a)

instance [DecidableEq n] (a : Option n) :
    IsOpenImmersion (toRelativeProjectiveSpaceChart S a) := by
  rw [toRelativeProjectiveSpaceChart]
  infer_instance

@[reassoc (attr := simp)]
lemma toRelativeProjectiveSpaceChart_over [DecidableEq n] (a : Option n) :
    toRelativeProjectiveSpaceChart S a ≫ ℙ(Option n; S) ↘ S = 𝔸(n; S) ↘ S := by
  simp [toRelativeProjectiveSpaceChart]

/-- A point of `ℙ(Option n; S)` lying over a point of `D₊(T_none) ⊆ ℙⁿ_ℤ` lies in the range
of the standard chart. -/
lemma mem_range_toRelativeProjectiveSpace (z : ℙ(Option n; S))
    (hz : ProjectiveSpace.toProjInt (Option n) S z ∈
      Proj.basicOpen (homogeneousSubmodule (Option n) (ULift.{u} ℤ)) (X none)) :
    z ∈ Set.range (toRelativeProjectiveSpace n S) := by
  rw [← Proj.opensRange_awayι _ _ isHomogeneous_X_none Nat.one_pos] at hz
  obtain ⟨y, hy⟩ := hz
  obtain ⟨y, rfl⟩ := (Spec.map (dehomogenizeEquiv n (ULift ℤ)).toCommRingCatIso.hom).surjective y
  obtain ⟨o, -, ho⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_toRelativeProjectiveSpace n S) y z hy
  exact ⟨o, ho⟩

/-- **The standard charts cover projective space**: every point of `ℙ(Option n; S)` lies in
the range of one of the charts `𝔸(n; S) ⟶ ℙ(Option n; S)` onto `D₊(T_a)`. -/
lemma exists_mem_range_toRelativeProjectiveSpaceChart [DecidableEq n] (z : ℙ(Option n; S)) :
    ∃ a : Option n, z ∈ Set.range (toRelativeProjectiveSpaceChart S a) := by
  have hz : ProjectiveSpace.toProjInt (Option n) S z ∈ (⊤ : TopologicalSpace.Opens _) := trivial
  rw [← Proj.iSup_basicOpen_X_eq_top, TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨a, ha⟩ := hz
  have hp : ProjectiveSpace.toProjInt (Option n) S z ∈
      Proj.renameMap (R := ULift.{u} ℤ) (Equiv.swap none a) ⁻¹ᵁ Proj.basicOpen _ (X none) := by
    rwa [Proj.renameMap_preimage_basicOpen, rename_X, Equiv.swap_apply_left]
  obtain ⟨o, ho⟩ := mem_range_toRelativeProjectiveSpace S
    (ProjectiveSpace.rename S (Equiv.swap none a) z) (by
      rw [← Scheme.Hom.comp_apply, ProjectiveSpace.rename_toProjInt, Scheme.Hom.comp_apply]
      exact hp)
  refine ⟨a, o, ?_⟩
  rw [toRelativeProjectiveSpaceChart, Scheme.Hom.comp_apply, ho, ← Scheme.Hom.comp_apply]
  simpa using congr($(ProjectiveSpace.rename_symm_comp S (Equiv.swap none a)) z)

end AffineSpace

namespace Compactification

variable {X S : Scheme.{u}} {n : Type u} [Finite n] {f : X ⟶ S}

lemma ofIsImmersionAffineSpace_g (i : X ⟶ 𝔸(n; S)) [IsImmersion i] [QuasiCompact f]
    (hi : i ≫ 𝔸(n; S) ↘ S = f) :
    (ofIsImmersionAffineSpace i hi).g =
      (i ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι ≫ ℙ(Option n; S) ↘ S :=
  rfl

/-- **The affine compactification locally embeds into affine space**: the compactification
of `X` obtained by closing up an immersion `X ⟶ 𝔸(n; S)` inside `ℙ(Option n; S)` is covered
by opens admitting immersions into `𝔸(n; S)` over `S`, namely its intersections with the
standard charts of `ℙ(Option n; S)`. -/
theorem locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace (i : X ⟶ 𝔸(n; S)) [IsImmersion i]
    [QuasiCompact f] (hi : i ≫ 𝔸(n; S) ↘ S = f) :
    (Compactification.ofIsImmersionAffineSpace i hi).g.LocallyEmbedsInAffineSpace
      (Nat.card n) := by
  classical
  intro z
  set ι := (i ≫ AffineSpace.toRelativeProjectiveSpace n S).imageι
  obtain ⟨a, y, hy⟩ := AffineSpace.exists_mem_range_toRelativeProjectiveSpaceChart S (ι z)
  set h := AffineSpace.toRelativeProjectiveSpaceChart S a
  set V : (ofIsImmersionAffineSpace i hi).Z.Opens := ι ⁻¹ᵁ h.opensRange
  have hV : Set.range (V.ι ≫ ι) ⊆ Set.range h := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have : IsImmersion (IsOpenImmersion.lift h (V.ι ≫ ι) hV ≫ h) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  refine ⟨V, ⟨y, hy⟩, n, inferInstance, IsOpenImmersion.lift h (V.ι ≫ ι) hV, le_rfl,
    .of_comp _ h, ?_⟩
  rw [← AffineSpace.toRelativeProjectiveSpaceChart_over S a, IsOpenImmersion.lift_fac_assoc,
    ofIsImmersionAffineSpace_g, Category.assoc]

end Compactification

end AlgebraicGeometry
