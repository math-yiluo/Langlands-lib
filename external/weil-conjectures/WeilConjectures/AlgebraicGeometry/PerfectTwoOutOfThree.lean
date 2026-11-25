/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectCommonAffineModels
import WeilConjectures.AlgebraicGeometry.PerfectAffineConeModel

/-! # Two out of three for perfect complexes on a scheme

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.7, Tag 08CR
(blueprint: lem-pc-perfect-two-out-of-three).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

private theorem perfect_of_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E F : schemeDerivedCategory X} (e : E ≅ F) (hE : IsPerfect X E) :
    IsPerfect X F := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨eK⟩⟩ := hE x
  exact ⟨U, hx, K, hK, ⟨((SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm) ≪≫ eK⟩⟩

private theorem perfect_shift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E : schemeDerivedCategory X} (hE : IsPerfect X E) (n : ℤ) :
    IsPerfect X (E⟦n⟧) := by
  intro x
  obtain ⟨U, hx, K, ⟨⟨a, b, hb⟩, hf⟩, ⟨eK⟩⟩ := hE x
  refine ⟨U, hx, K⟦n⟧, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨a - n, b - n, fun i hi ↦ ?_⟩
    exact hb (i + n) (by omega)
  · exact fun i ↦ hf (i + n)
  · let F := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    exact ⟨(F.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso eK ≪≫
      ((DerivedCategory.Q.commShiftIso n).app K).symm⟩

/-- In a distinguished triangle of `D(𝒪_X)`, any two perfect terms force the third to be
perfect. Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.7, Tag 08CR
(blueprint: lem-pc-perfect-two-out-of-three).

Proof: By `lemma-coherent-base-change-invertible-sheaves--1`, intersect and refine the local covers
of the two perfect terms to a common affine cover. Restriction is exact and preserves cone triangles
(`def-weil-abstract-derived-category`). On each affine open, Tag 08EB represents both
perfect terms by bounded complexes of finite projective modules.

If the first two terms are perfect, `lem-pc-affine-qcoh-derived-equivalence` lifts their
arrow to the module derived category, and `lem-sc-affine-projective-complex-derived-hom`
represents it by a chain map. Its cone is bounded, with terms the direct sums of the second
complex's terms and shifted terms of the first, hence finite projective. Sheafification
commutes with that cone. TR3 (`def-weil-triangulated-category`) extends the first two
isomorphisms to a triangle morphism; `lem-sf-triangle-morphism-iso` makes the third component
an isomorphism. Thus the third term is locally represented by a strictly perfect complex.

If the last two terms are perfect, rotate the triangle by TR2 and apply the first case;
then shift back. If the first and last terms are perfect, rotate backwards, apply the first
case to the shifted last term and the first term, and obtain the middle term. Shifts preserve
bounded finite projective complexes. Finally the local conclusions on the common affine
cover imply perfectness on `X` by `lemma-coherent-base-change-invertible-sheaves--1`. -/
theorem isPerfect_two_out_of_three (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Triangle (schemeDerivedCategory X)) (hT : T ∈ distTriang (schemeDerivedCategory X)) :
    (IsPerfect X T.obj₁ → IsPerfect X T.obj₂ → IsPerfect X T.obj₃) ∧
      (IsPerfect X T.obj₂ → IsPerfect X T.obj₃ → IsPerfect X T.obj₁) ∧
      (IsPerfect X T.obj₁ → IsPerfect X T.obj₃ → IsPerfect X T.obj₂) := by
  have hcone (S : Triangle (schemeDerivedCategory X))
      (hS : S ∈ distTriang (schemeDerivedCategory X))
      (h₁ : IsPerfect X S.obj₁) (h₂ : IsPerfect X S.obj₂) : IsPerfect X S.obj₃ := by
    intro x
    obtain ⟨U, hx, hU, A, B, hA, hB, eA, eB⟩ :=
      perfect_common_affine_models X S.obj₁ S.obj₂ h₁ h₂ x
    obtain ⟨K, hK, eK⟩ := perfect_affine_cone_model X U hU S hS A B hA hB eA eB
    exact ⟨U, hx, K, hK, eK⟩
  refine ⟨hcone T hT, ?_, ?_⟩
  · intro h₂ h₃
    have hshift : IsPerfect X (T.obj₁⟦(1 : ℤ)⟧) :=
      hcone T.rotate (rot_of_distTriang T hT) h₂ h₃
    exact perfect_of_iso X ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app T.obj₁)
      (perfect_shift X hshift (-1))
  · intro h₁ h₃
    exact hcone T.invRotate (inv_rot_of_distTriang T hT) (perfect_shift X h₃ (-1)) h₁

end AlgebraicGeometry.Scheme
