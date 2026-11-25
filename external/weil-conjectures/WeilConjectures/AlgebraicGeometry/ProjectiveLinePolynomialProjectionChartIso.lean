/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection

/-!
# Polynomial projective-line projection on standard charts

Source: Stacks Project, Constructions, Tag 01NG and its base change to Spec k.
(blueprint: lem-sc-p1-polynomial-projection-chart-iso)
-/

@[expose] public section

universe v

open CategoryTheory MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical linear projection of polynomial Proj is an isomorphism when
restricted to either standard affine chart of the projective line.
Source: Stacks Project, Constructions, Tag 01NG, base changed to Spec k.
(blueprint: lem-sc-p1-polynomial-projection-chart-iso)

Proof: by linearProjection_preimage_standardOpen, the source of the restriction
is D₊(xᵢ). Identify it with Spec of the homogeneous localization at xᵢ, and
identify the target standard open with affine space over Spec k. The chart
formula awayι_linearProjection and homOfSections_resLE_standardOpenIso_hom
identify the restricted map with the affine-coordinate map sending the other
coordinate to xⱼ/xᵢ. The homogeneousLocalizationAwayXEquiv identifies the source
ring with the polynomial ring in that ratio, so this map is an isomorphism.
Reindex the complementary variables from Fin 2 to ULift (Fin 2); the down map
is a bijection and induces the corresponding polynomial-ring isomorphism.
Conjugating by these source and target chart isomorphisms proves the claim. -/
theorem isIso_polynomial_linearProjection_restrict (k : Type v) [Field k]
    (hcov : (⨆ i : ULift.{v} (Fin 2),
      basicOpen (homogeneousSubmodule (Fin 2) k) (X i.down)) = ⊤)
    (i : ULift.{v} (Fin 2)) :
    IsIso (linearProjection (homogeneousSubmodule (Fin 2) k)
      (fun j : ULift.{v} (Fin 2) ↦ X j.down)
      (fun j ↦ X_mem_homogeneousSubmodule_one k j.down) hcov ∣_
        ProjectiveSpace.standardOpen (ULift.{v} (Fin 2)) (Spec (.of k)) i) := by
  classical
  let ι := ULift.{v} (Fin 2)
  let 𝒜 := homogeneousSubmodule (Fin 2) k
  let l : ι → MvPolynomial (Fin 2) k := fun j ↦ X j.down
  let hl : ∀ j, l j ∈ 𝒜 1 := fun j ↦ X_mem_homogeneousSubmodule_one k j.down
  change IsIso (linearProjection 𝒜 l hl hcov ∣_
    ProjectiveSpace.standardOpen ι (Spec (.of k)) i)
  obtain ⟨e, key⟩ := exists_iso_linearProjection_restrict 𝒜 l hl hcov i
  let re : {j : Fin 2 // j ≠ i.down} ≃ {j : ι // j ≠ i} :=
    { toFun := fun j ↦ ⟨⟨j.1⟩, fun h ↦ j.2 (congrArg ULift.down h)⟩
      invFun := fun j ↦ ⟨j.1.down, fun h ↦ j.2 (ULift.ext h)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let E : Away 𝒜 (l i) ≃ₐ[k] MvPolynomial {j : ι // j ≠ i} k :=
    (homogeneousLocalizationAwayXEquiv k i.down).trans (renameEquiv k re)
  have hvec : AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (l i)))))
      (fun j : {j : ι // j ≠ i} ↦ (Scheme.ΓSpecIso (.of (Away 𝒜 (l i)))).inv
        (Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1))) =
      Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
        (AffineSpace.SpecIso {j : ι // j ≠ i} (.of k)).inv := by
    apply AffineSpace.hom_ext
    · rw [AffineSpace.homOfVector_over, Category.assoc, AffineSpace.SpecIso_inv_over,
        ← Spec.map_comp]
      congr 1
      ext x : 2
      exact (E.symm.commutes x).symm
    · intro j
      rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord,
        ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      congr 1
      change Away.mk 𝒜 (hl i) 1 (l j.1) _ = E.symm (X j)
      change Away.mk 𝒜 (hl i) 1 (l j.1) _ =
        (homogeneousLocalizationAwayXEquiv k i.down).symm
          ((renameEquiv k re).symm (X j))
      rw [renameEquiv_symm, renameEquiv_apply, rename_X]
      exact (homogeneousLocalizationAwayXEquiv_symm_X k i.down (re.symm j)).symm
  have : IsIso (Spec.map (CommRingCat.ofHom E.symm.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom E.symm.toRingHom) :=
      inferInstanceAs (IsIso E.symm.toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  have : IsIso (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (l i)))))
      (fun j : {j : ι // j ≠ i} ↦ (Scheme.ΓSpecIso (.of (Away 𝒜 (l i)))).inv
        (Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1)))) := by
    rw [hvec]
    infer_instance
  have : IsIso (e.hom ≫ (linearProjection 𝒜 l hl hcov ∣_
      ProjectiveSpace.standardOpen ι (Spec (.of k)) i) ≫
      (ProjectiveSpace.standardOpenIso ι (Spec (.of k)) i).hom) := by
    rw [key]
    infer_instance
  have : IsIso ((linearProjection 𝒜 l hl hcov ∣_
      ProjectiveSpace.standardOpen ι (Spec (.of k)) i) ≫
      (ProjectiveSpace.standardOpenIso ι (Spec (.of k)) i).hom) :=
    IsIso.of_isIso_comp_left e.hom _
  exact IsIso.of_isIso_comp_right _
    (ProjectiveSpace.standardOpenIso ι (Spec (.of k)) i).hom


end AlgebraicGeometry.Proj
