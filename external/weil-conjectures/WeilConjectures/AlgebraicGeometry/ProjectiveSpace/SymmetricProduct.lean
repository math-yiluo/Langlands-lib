/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct.Multiplication
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Zero

/-!
# The symmetric product morphism `(ℙ¹)ⁿ ⟶ ℙⁿ`

For a scheme `S` and `n : ℕ`, write `(ℙ¹_S)ⁿ` for the `n`-fold fibre power of the projective
line over `S`, realised as the tower `ℙ¹_{ℙ¹_{⋯ S}}`
(`AlgebraicGeometry.ProjectiveSpace.projectiveLinePow`). The polynomials `F₀, …, Fₙ` defined by

`∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tʲ`

are multihomogeneous of degree one in every pair `(xᵢ, yᵢ)`, have no common zero and are
invariant under permutation of the factors; they define the *symmetric product morphism*
`σₙ : (ℙ¹_S)ⁿ ⟶ ℙⁿ_S`, which is finite and surjective. Over an algebraically closed field this
says that a binary form of degree `n` factors as a product of `n` linear forms.

This is the step from `ℙ¹` to `ℙⁿ` in the reduction of proper base change to the projective
line.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.projectiveLinePow`: the tower `(ℙ¹_S)ⁿ`.
- `AlgebraicGeometry.ProjectiveSpace.projectiveLinePowProj`: its projection to `S`.
- `AlgebraicGeometry.ProjectiveSpace.symmetricProduct`: the symmetric product morphism
  `σₖ : (ℙ¹_S)ᵏ ⟶ ℙ(ι; S)` for `ι ≃ Fin (k + 1)`, defined recursively as
  `σₖ₊₁ = ℙ¹_{σₖ} ≫ μ` for the multiplication morphism `μ : ℙ¹_{ℙᵏ_S} ⟶ ℙᵏ⁺¹_S` of
  `AlgebraicGeometry.ProjectiveSpace.projectiveLineMul`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.symmetricProduct_over`,
  `AlgebraicGeometry.ProjectiveSpace.isFinite_symmetricProduct`,
  `AlgebraicGeometry.ProjectiveSpace.surjective_symmetricProduct`: `σₖ` is a finite surjective
  morphism over `S`.
- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_surjective_projectiveLinePow`: for every
  finite nonempty index type `n` there are `k` and a finite surjective morphism
  `(ℙ¹_S)ᵏ ⟶ ℙ(n; S)` over `S`.

## Implementation details

`σₖ₊₁` is the composite of `ℙ¹_{σₖ}` with the multiplication morphism
`((x: y), ∑ⱼ Gⱼ tʲ) ↦ (x t + y) · ∑ⱼ Gⱼ tʲ`, so finiteness and surjectivity follow by induction
from those of the multiplication morphism, with no Noetherian hypothesis on `S`.

## References

- Stacks Project, proof of Lemma 59.91.10, <https://stacks.math.columbia.edu/tag/0A4F>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- The `n`-fold fibre power `(ℙ¹_S)ⁿ` of the projective line over `S`, realised as the tower
`(ℙ¹_S)⁰ = S` and `(ℙ¹_S)ⁿ⁺¹ = ℙ¹_{(ℙ¹_S)ⁿ}`. -/
noncomputable def projectiveLinePow : ℕ → Scheme.{u} → Scheme.{u}
  | 0, S => S
  | n + 1, S => ProjectiveLine (projectiveLinePow n S)

/-- The projection `(ℙ¹_S)ⁿ ⟶ S`, the composite of the projections of the projective lines of
the tower `AlgebraicGeometry.ProjectiveSpace.projectiveLinePow`. -/
noncomputable def projectiveLinePowProj : (n : ℕ) → (S : Scheme.{u}) → projectiveLinePow n S ⟶ S
  | 0, S => 𝟙 S
  | n + 1, S => (ProjectiveLine (projectiveLinePow n S) ↘ projectiveLinePow n S) ≫
      projectiveLinePowProj n S


/-- **The symmetric product morphism** `σₖ: (ℙ¹_S)ᵏ ⟶ ℙ(ι; S)` for an index type `ι` with
`k + 1` elements (numbered by `e: ι ≃ Fin (k + 1)`): a point `((xᵢ: yᵢ))ᵢ` is sent to
`[F₀: ⋯: Fₖ]`, where `∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tʲ`, the coordinate `F_{e c}` being the
homogeneous coordinate `c`. -/
noncomputable def symmetricProduct (S : Scheme.{u}) :
    (k : ℕ) → {ι : Type u} → (ι ≃ Fin (k + 1)) → (projectiveLinePow k S ⟶ ℙ(ι; S))
  | 0, ι, e =>
    letI : Unique ι := @Equiv.unique _ (Fin 1) _ e
    haveI := instIsIso ι S
    inv (ℙ(ι; S) ↘ S)
  | k + 1, _, e => map (ULift.{u} (Fin 2)) (symmetricProduct S k Equiv.ulift) ≫
      projectiveLineMul e S

/-- **The symmetric product morphism is a morphism over `S`**: composed with the structure
morphism of `ℙ(ι; S)` it is the projection `(ℙ¹_S)ᵏ ⟶ S`. -/
@[reassoc (attr := simp)]
theorem symmetricProduct_over (S : Scheme.{u}) (k : ℕ) {ι : Type u} (e : ι ≃ Fin (k + 1)) :
    symmetricProduct S k e ≫ ℙ(ι; S) ↘ S = projectiveLinePowProj k S := by
  induction k generalizing ι with
  | zero =>
    have : Unique ι := @Equiv.unique _ (Fin 1) _ e
    have := instIsIso ι S
    simp only [symmetricProduct]
    exact IsIso.inv_hom_id _
  | succ k ih =>
    rw [symmetricProduct, Category.assoc, projectiveLineMul_over, map_over_assoc, ih]
    rfl

/-- **The symmetric product morphism is finite.** -/
theorem isFinite_symmetricProduct (S : Scheme.{u}) (k : ℕ) {ι : Type u}
    (e : ι ≃ Fin (k + 1)) : IsFinite (symmetricProduct S k e) := by
  induction k generalizing ι with
  | zero =>
    have : Unique ι := @Equiv.unique _ (Fin 1) _ e
    have := instIsIso ι S
    rw [symmetricProduct]
    infer_instance
  | succ k ih =>
    have := ih Equiv.ulift
    have : IsFinite (map (ULift.{u} (Fin 2)) (symmetricProduct S k Equiv.ulift)) :=
      MorphismProperty.of_isPullback (isPullback_map _ _).flip inferInstance
    rw [symmetricProduct]
    infer_instance

/-- **The symmetric product morphism is surjective.** -/
theorem surjective_symmetricProduct (S : Scheme.{u}) (k : ℕ) {ι : Type u}
    (e : ι ≃ Fin (k + 1)) : Surjective (symmetricProduct S k e) := by
  induction k generalizing ι with
  | zero =>
    have : Unique ι := @Equiv.unique _ (Fin 1) _ e
    have := instIsIso ι S
    rw [symmetricProduct]
    infer_instance
  | succ k ih =>
    have := ih Equiv.ulift
    have : Surjective (map (ULift.{u} (Fin 2)) (symmetricProduct S k Equiv.ulift)) :=
      MorphismProperty.of_isPullback (P := @Surjective) (isPullback_map _ _).flip inferInstance
    rw [symmetricProduct]
    infer_instance

/-- **The symmetric product morphism is finite and surjective.** For a finite nonempty index
type `n` with `k + 1` elements there is a finite surjective morphism `σ: (ℙ¹_S)ᵏ ⟶ ℙ(n; S)` over
`S`: the symmetric product morphism `((xᵢ: yᵢ))ᵢ ↦ [F₀: ⋯: Fₖ]` with
`∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tʲ` (`AlgebraicGeometry.ProjectiveSpace.symmetricProduct`). -/
theorem exists_isFinite_surjective_projectiveLinePow (n : Type u) [Finite n] [Nonempty n]
    (S : Scheme.{u}) :
    ∃ (k : ℕ) (σ : projectiveLinePow k S ⟶ ℙ(n; S)), IsFinite σ ∧ Surjective σ ∧
      σ ≫ ℙ(n; S) ↘ S = projectiveLinePowProj k S := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin n
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
    Nat.exists_eq_add_one.mpr (Fin.pos_iff_nonempty.mpr (e.symm.nonempty))
  exact ⟨k, symmetricProduct S k e, isFinite_symmetricProduct S k e,
    surjective_symmetricProduct S k e, symmetricProduct_over S k e⟩

/-- For a scheme `S` and `n = k + 1 ≥ 1`, with `ι` a type with `n + 1` elements indexing the
homogeneous coordinates of `ℙⁿ_S`, the symmetric product morphism `σₙ: (ℙ¹_S)ⁿ ⟶ ℙⁿ_S` is
finite and surjective. -/
theorem isFinite_and_surjective_symmetricProduct (S : Scheme.{u}) (k : ℕ) {ι : Type u}
    (e : ι ≃ Fin (k + 1 + 1)) :
    IsFinite (symmetricProduct S (k + 1) e) ∧ Surjective (symmetricProduct S (k + 1) e) :=
  ⟨isFinite_symmetricProduct S (k + 1) e, surjective_symmetricProduct S (k + 1) e⟩


end AlgebraicGeometry.ProjectiveSpace
