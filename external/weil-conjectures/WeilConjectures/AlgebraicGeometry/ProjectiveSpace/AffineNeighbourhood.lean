/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Affine neighbourhoods of finite sets in quasi-projective schemes

In a quasi-projective scheme over a field every finite set of points lies in an affine open
(Stacks 01ZY, 09NN).

## Main statements

- `AlgebraicGeometry.exists_isAffineOpen_superset_of_isImmersion_of_isAffine`: if `X` is
  quasi-compact and quasi-separated and admits a quasi-compact immersion into `ℙ(α; S)` with `S`
  affine, every finite set of points of `X` lies in an affine open.
- `AlgebraicGeometry.exists_isAffineOpen_superset_of_isImmersion`: the same for any immersion
  into `ℙ(α; Spec K)` with `K` a field.
- `AlgebraicGeometry.IsQuasiProjective.exists_isAffineOpen_superset`: every finite set of points
  of a quasi-projective scheme over a field lies in an affine open.

## Proof

The immersion can be replaced by a morphism `ψ : X ⟶ ℙ(β; S)` whose preimages of the standard
opens are affine (`AlgebraicGeometry.exists_isAffineOpen_preimage_of_isImmersion`), so `ψ` is an
affine morphism, as is `ℙ(β; S) ⟶ ℙ^β_ℤ`. Graded prime avoidance gives a form `G` over `ℤ` of
positive degree not vanishing at the images of the finitely many points; the preimage of the
affine open `D₊(G)` is the required affine open.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Let `S` be affine and let `X` be a quasi-compact quasi-separated scheme with a quasi-compact
immersion `j : X ⟶ ℙ(α; S)`. Then every finite set of points of `X` lies in an affine open. -/
theorem exists_isAffineOpen_superset_of_isImmersion_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    {α : Type u} [Finite α] (j : X ⟶ ℙ(α; S)) [IsImmersion j] [QuasiCompact j] [CompactSpace X]
    [QuasiSeparatedSpace X] (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  classical
  obtain ⟨β, _, ψ, -, hψ⟩ := exists_isAffineOpen_preimage_of_isImmersion j
  have hψa : IsAffineHom ψ := HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
    (fun b ↦ ⟨_, ProjectiveSpace.isAffineOpen_standardOpen β S b⟩)
    (ProjectiveSpace.iSup_standardOpen _ _) fun b ↦ hψ b
  have hτ : IsAffineHom (ProjectiveSpace.toProjInt β S) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  set 𝒜 := MvPolynomial.homogeneousSubmodule β (ULift.{u} ℤ)
  let ρ := ψ ≫ ProjectiveSpace.toProjInt β S
  obtain ⟨d, hd, G, hG, hGs⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset (hs.toFinset.image ρ)
  refine ⟨ρ ⁻¹ᵁ Proj.basicOpen 𝒜 G,
    ((Proj.isAffineOpen_basicOpen 𝒜 G hG hd).preimage _).preimage ψ, fun x hx ↦ ?_⟩
  exact hGs (ρ x) (Finset.mem_image_of_mem _ (by simpa using hx))

/-- **Finite sets in quasi-projective schemes lie in affine opens** (Stacks 01ZY, 09NN). If `X`
admits an immersion into `ℙ(α; Spec K)` for a field `K`, then every finite set of points of `X`
lies in an affine open. -/
@[stacks 01ZY]
theorem exists_isAffineOpen_superset_of_isImmersion {K : Type u} [Field K] {X : Scheme.{u}}
    {α : Type u} [Finite α] (i : X ⟶ ℙ(α; Spec (.of K))) [IsImmersion i]
    (s : Set X) (hs : s.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  have : IsLocallyNoetherian ℙ(α; Spec (.of K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(α; Spec (.of K)) ↘ Spec (.of K))
  have : QuasiCompact i := by
    rw [← i.liftCoborder_ι]
    infer_instance
  have : CompactSpace ℙ(α; Spec (.of K)) :=
    QuasiCompact.compactSpace_of_compactSpace (ℙ(α; Spec (.of K)) ↘ Spec (.of K))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated i
  exact exists_isAffineOpen_superset_of_isImmersion_of_isAffine i s hs

/-- **Finite sets in quasi-projective schemes lie in affine opens** (Stacks 01ZY, 09NN). Every
finite set of points of a quasi-projective scheme over a field lies in an affine open. -/
@[stacks 09NN]
theorem IsQuasiProjective.exists_isAffineOpen_superset {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} (hf : IsQuasiProjective f) (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  obtain ⟨β, _, i, hi, -⟩ := hf
  exact exists_isAffineOpen_superset_of_isImmersion i s hs

end AlgebraicGeometry
