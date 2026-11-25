/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus

/-!
# Splitting a complex of matrices in one degree from ranks at a point

Let `A₀, A₁, A₂, A₃` be composable matrices of global functions on a scheme `X` with vanishing
consecutive products. If at a point `y` the fibre of the complex is exact at the source of `A₁`
and at the target of `A₂`, and its cohomology between `A₁` and `A₂` has dimension `k`, then on a
neighbourhood of `y` the middle term is split with cohomology free of rank `k`
(`AlgebraicGeometry.Scheme.exists_opens_hasSplitHomology_of_rank_add_eq`).

This is the degree-by-degree form of `AlgebraicGeometry.Scheme.exists_opens_hasSplitHomology`,
where the matrices need not come from a single complex: it allows to replace the incoming
differential by a matrix defined only near `y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **Splitting near a point in one degree.** Let `A₁ A₀ = 0`, `A₂ A₁ = 0`, `A₃ A₂ = 0` for
matrices of global functions on `X`, and `y` a point at which
`rank A₀(y) + rank A₁(y) = |ι₀|`, `rank A₁(y) + rank A₂(y) + k = |ι₁|` and
`rank A₂(y) + rank A₃(y) = |ι₂|`. Then on an open neighbourhood `W` of `y`, after pulling back
along any `g : Z ⟶ X` with image in `W`, the middle term of `A₁` and `A₂` is split with
cohomology free of rank `k`. -/
theorem exists_opens_hasSplitHomology_of_rank_add_eq {κ ι₀ ι₁ ι₂ ι₃ : Type*} [Fintype κ]
    [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Finite ι₃] [DecidableEq ι₁]
    (A₀ : Matrix ι₀ κ Γ(X, ⊤)) (A₁ : Matrix ι₁ ι₀ Γ(X, ⊤))
    (A₂ : Matrix ι₂ ι₁ Γ(X, ⊤)) (A₃ : Matrix ι₃ ι₂ Γ(X, ⊤)) (h₁₀ : A₁ * A₀ = 0)
    (h₂₁ : A₂ * A₁ = 0) (h₃₂ : A₃ * A₂ = 0) {y : X} {k : ℕ}
    (h₀ : (A₀.map (X.fromSpecResidueField y).appTop).rank +
      (A₁.map (X.fromSpecResidueField y).appTop).rank = Fintype.card ι₀)
    (h₁ : (A₁.map (X.fromSpecResidueField y).appTop).rank +
      (A₂.map (X.fromSpecResidueField y).appTop).rank + k = Fintype.card ι₁)
    (h₂ : (A₂.map (X.fromSpecResidueField y).appTop).rank +
      (A₃.map (X.fromSpecResidueField y).appTop).rank = Fintype.card ι₂) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ X), Set.range g ⊆ W →
      Matrix.HasSplitHomology (A₁.map g.appTop) (A₂.map g.appTop) (Fin k) := by
  classical
  have := Fintype.ofFinite ι₃
  -- split factorisations of the two differentials near `y`
  obtain ⟨Wa, hya, ha⟩ := exists_opens_split_of_rank_add_eq _ _ h₁₀ y h₀
  obtain ⟨Wb, hyb, hb⟩ := exists_opens_split_of_rank_add_eq _ _ h₃₂ y h₂
  set W₁ := Wa ⊓ Wb with hW₁
  obtain ⟨-, -, -, -, L₁, M₁, L₁', M₁', -, s₁, -⟩ := ha W₁.ι (by
    rw [Opens.range_ι]
    exact fun z hz ↦ hz.1)
  obtain ⟨L₂, M₂, L₂', M₂', -, -, -, -, s₂, -, -⟩ := hb W₁.ι (by
    rw [Opens.range_ι]
    exact fun z hz ↦ hz.2)
  have hA : A₂.map W₁.ι.appTop * A₁.map W₁.ι.appTop = 0 := by
    rw [← Matrix.map_mul, h₂₁, Matrix.map_zero _ (map_zero _)]
  have hML := Matrix.mul_eq_zero_of_split hA s₁.1 s₁.2.2 s₂.1 s₂.2.1
  set ε := Matrix.splitIdempotent L₁ L₁' M₂ M₂' with hε
  have he : ε * ε = ε := Matrix.splitIdempotent_mul_self s₁.2.1 s₂.2.2 hML
  set y₁ : W₁.toScheme := ⟨y, hya, hyb⟩
  -- the rank of the idempotent `ε` at `y` is `k`
  have hrank : (ε.map (W₁.toScheme.fromSpecResidueField y₁).appTop).rank = k := by
    let := (Modules.isField_Γ_Spec_residueField y₁).toField
    have := Modules.rank_splitIdempotent_map hA s₁ s₂
      (W₁.toScheme.fromSpecResidueField y₁).appTop.hom
    rw [hε]
    refine this.trans ?_
    omega
  have hrank' : (ε.map (W₁.toScheme.fromSpecResidueField y₁).appTop).rank +
      ((1 - ε).map (W₁.toScheme.fromSpecResidueField y₁).appTop).rank = Fintype.card ι₁ := by
    let := (Modules.isField_Γ_Spec_residueField y₁).toField
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.rank_add_rank_one_sub (by rw [← Matrix.map_mul, he])
  obtain ⟨W₂, hyW₂, hc⟩ := exists_opens_split_of_rank_add_eq ε (1 - ε)
    (by rw [Matrix.sub_mul, he, Matrix.one_mul, sub_self]) y₁ hrank'
  refine ⟨W₁.ι ''ᵁ W₂, ⟨y₁, hyW₂, rfl⟩, fun g hg ↦ ?_⟩
  have hg₁ : Set.range g ⊆ Set.range W₁.ι := by
    refine hg.trans ?_
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  set g₁ := IsOpenImmersion.lift W₁.ι g hg₁
  have hfac : g₁ ≫ W₁.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hg₂ : Set.range g₁ ⊆ W₂ := by
    rintro _ ⟨z, rfl⟩
    rw [← Hom.preimage_image_eq W₁.ι W₂]
    change W₁.ι (g₁ z) ∈ W₁.ι ''ᵁ W₂
    rw [← Hom.comp_apply, hfac]
    exact hg ⟨z, rfl⟩
  obtain ⟨L₃, M₃, L₃', M₃', -, -, -, -, s₃, -, -⟩ := hc g₁ hg₂
  -- everything pulled back along `g₁`
  have t₁ := Matrix.split_map g₁.appTop.hom s₁
  have t₂ := Matrix.split_map g₁.appTop.hom s₂
  have c₁ : (A₁.map W₁.ι.appTop).map g₁.appTop.hom = A₁.map g.appTop := by
    rw [← hfac, Modules.map_appTop_comp]
  have c₂ : (A₂.map W₁.ι.appTop).map g₁.appTop.hom = A₂.map g.appTop := by
    rw [← hfac, Modules.map_appTop_comp]
  rw [c₁] at t₁
  rw [c₂] at t₂
  have hε₃ := s₃.1
  have hεmap : ε.map g₁.appTop = Matrix.splitIdempotent (L₁.map g₁.appTop.hom)
      (L₁'.map g₁.appTop.hom) (M₂.map g₁.appTop.hom) (M₂'.map g₁.appTop.hom) :=
    Matrix.splitIdempotent_map _
  rw [hεmap] at hε₃
  have h₃ : M₃ * L₃ = 1 := by
    refine Matrix.mul_eq_one_of_isIdempotentElem ?_ s₃.2.1 s₃.2.2
    rw [← s₃.1, ← Matrix.map_mul, he]
  have hA' : A₂.map g.appTop * A₁.map g.appTop = 0 := by
    rw [← Matrix.map_mul, h₂₁, Matrix.map_zero _ (map_zero _)]
  exact (Matrix.hasSplitHomology_of_splitIdempotent hA' t₁ t₂ hε₃ h₃).of_equiv (finCongr hrank)

end AlgebraicGeometry.Scheme
