import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # A finite family of global sections over a field through a linearly independent family -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- For a scheme `X` over `Spec k`, `k` a field, the structure map `⊤ ⟶ ⊤` on global sections
used by `Scheme.TwoAffineOpenCover.algebraOfHom c ⊤` is `c.appTop`. -/
theorem appLE_top_top {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) :
    c.appLE ⊤ ⊤ le_top = c.appTop := by
  simp [Scheme.Hom.appLE]
  exact Category.comp_id (c.app ⊤)

/-- The ring homomorphism from `k` to the global sections of a scheme `X` over `Spec k`:
the inverse of `Γ(Spec k) ≅ k` followed by pullback of global sections along `c`. -/
noncomputable def globalScalars {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) :
    k →+* Γ(X, ⊤) :=
  c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem globalScalars_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of k)) (r : k) :
    globalScalars c r = c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) :=
  rfl

/-- The algebra map of `Scheme.TwoAffineOpenCover.algebraOfHom c ⊤` is `globalScalars c`. -/
theorem algebraMap_algebraOfHom_top {k : Type u} [Field k] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of k)) :
    @algebraMap k Γ(X, ⊤) _ _ (Scheme.TwoAffineOpenCover.algebraOfHom c ⊤) = globalScalars c := by
  ext r
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, appLE_top_top]
  rfl

/-- A finite family of global sections of a scheme `X` over `Spec k`, `k` a field, is a
combination, with coefficients pulled back from `k` along the structure map, of a finite family of
global sections that is linearly independent for the `k`-algebra structure
`Scheme.TwoAffineOpenCover.algebraOfHom c ⊤`. -/
theorem exists_linearIndependent_sum_appTop_mul {k : Type u} [Field k] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of k)) {C : Type*} [Finite C] (w : C → Γ(X, ⊤)) :
    ∃ (m : ℕ) (e : Fin m → Γ(X, ⊤)) (r : C → Fin m → k),
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤; LinearIndependent k e) ∧
      ∀ κ, w κ = ∑ l, c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (r κ l)) * e l := by
  let _ := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
  let V := Submodule.span k (Set.range w)
  have : FiniteDimensional k V := FiniteDimensional.span_of_finite k (Set.finite_range w)
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun l => (b l : Γ(X, ⊤)),
    fun κ l => b.repr ⟨w κ, Submodule.subset_span ⟨κ, rfl⟩⟩ l, ?_, ?_⟩
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · intro κ
    have h := congrArg Subtype.val (b.sum_repr ⟨w κ, Submodule.subset_span ⟨κ, rfl⟩⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, Algebra.smul_def, algebraMap_algebraOfHom_top,
      globalScalars_apply] at h
    exact h.symm

end Langlands.AlgebraicGeometry
