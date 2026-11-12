import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq

/-! # Affine schemes of finite type in a standard open of projective space

An affine scheme `W` of finite type over `Spec C` is a closed subscheme of the standard affine
open `D₊(X₀) = Spec (C[X₀, …, Xₙ]_{(X₀)})` of projective space `ℙⁿ_C`, for some `n`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine open `Spec (C[X₀, …, Xₙ]_{(X₀)})` of projective space. -/
abbrev stdAway (C : Type u) [CommRing C] (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) C)
    (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) C))

/-- The open immersion of the standard affine open `D₊(X₀)` into projective space. -/
abbrev stdAwayι (C : Type u) [CommRing C] (n : ℕ) :
    Spec (stdAway C n) ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) C) :=
  Proj.awayι (homogeneousSubmodule (Fin (n + 1)) C) (MvPolynomial.X 0)
    (ProjSpace.X_mem_one C n 0) one_pos

/-- An affine scheme of finite type over `Spec C` is a closed subscheme of the standard affine
open `D₊(X₀)` of some projective space over `C`, compatibly with the structure morphisms. -/
theorem exists_closedImmersion_stdAway (C : Type u) [CommRing C] {W : Scheme.{u}} [IsAffine W]
    (s : W ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType s] :
    ∃ (n : ℕ) (ι : W ⟶ Spec (stdAway C n)), IsClosedImmersion ι ∧
      ι ≫ stdAwayι C n ≫ ProjSpace.π C n = s := by
  classical
  let f : CommRingCat.of C ⟶ Γ(W, ⊤) := (Scheme.ΓSpecIso _).inv ≫ s.appTop
  have hs : s = W.isoSpec.hom ≫ Spec.map f := by
    have h := Scheme.isoSpec_hom_naturality s
    rw [Scheme.isoSpec_Spec_hom] at h
    rw [Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hft : f.hom.FiniteType := by
    have h1 : (s.appTop).hom.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv).2
    exact h1.comp h2
  let : Algebra C Γ(W, ⊤) := f.hom.toAlgebra
  have : Algebra.FiniteType C Γ(W, ⊤) := hft
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := C) (A := Γ(W, ⊤))
  let n := t.card
  let b : Fin (n + 1) → Γ(W, ⊤) := Fin.cons 1 fun k => (t.equivFin.symm k : Γ(W, ⊤))
  obtain ⟨φ, hφ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq C n 0 b rfl
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← ht, Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨ProjSpace.ratio C n 0 (t.equivFin ⟨x, hx⟩).succ, ?_⟩
    change φ _ = x
    rw [hφ]
    simp [b]
  refine ⟨n, W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hsurj
    infer_instance
  · rw [hs, ProjSpace.awayι_comp_π, Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact φ.commutes x

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
