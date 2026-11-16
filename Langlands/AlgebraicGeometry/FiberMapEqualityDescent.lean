import Langlands.Algebra.FiberMapEqualityLocus
import Langlands.AlgebraicGeometry.ConstructibleAffineLimit
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

/-! # Coefficient enlargement preserving equality on every residue fibre -/

noncomputable section

universe u

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.FiberMapEqualityDescent

variable {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra R₀ R]

/-- A constructible condition true over the whole limit spectrum is true over
one finitely generated coefficient algebra containing any prescribed finite set. -/
theorem exists_fg_subalgebra_preimage_eq_univ
    (s : Set (PrimeSpectrum R₀)) (hs : IsConstructible s)
    (H : PrimeSpectrum.comap (algebraMap R₀ R) ⁻¹' s = Set.univ) (t : Finset R) :
    ∃ T : Subalgebra R₀ R, T.FG ∧ (↑t : Set R) ⊆ T ∧
      PrimeSpectrum.comap (algebraMap R₀ T) ⁻¹' s = Set.univ := by
  classical
  let ι : Type u := {T : Subalgebra R₀ R // T.FG ∧ (↑t : Set R) ⊆ T}
  let i₀ : ι := ⟨Algebra.adjoin R₀ ↑t, Subalgebra.fg_adjoin_finset t,
    Algebra.subset_adjoin⟩
  let : Nonempty ι := ⟨i₀⟩
  let : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1,
      T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1),
      (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : ι →o Subalgebra R₀ R := ⟨fun T => T.1, fun _ _ h => h⟩
  have hS : ∀ a : R, ∃ i, a ∈ S i := fun a =>
    ⟨⟨Algebra.adjoin R₀ ↑(insert a t), Subalgebra.fg_adjoin_finset _,
      fun x hx => Algebra.subset_adjoin (by simp [hx])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ :=
    P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.nonempty_isLimit_specCone S hS
  let D := SubalgebraStages.specDiagram S
  let c := SubalgebraStages.specCone S
  let : ∀ {i j : ιᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) := fun _ => by
    dsimp [D, SubalgebraStages.specDiagram, SubalgebraStages.specTrans]
    infer_instance
  let s₀ : Set (D.obj (op i₀)) := (SubalgebraStages.specHom S i₀) ⁻¹' s
  have hs₀ : IsConstructible s₀ :=
    (SubalgebraStages.specHom S i₀).isConstructible_preimage hs
  have hfull : (c.π.app (op i₀)) ⁻¹' s₀ = Set.univ := by
    change (SubalgebraStages.specLeg S i₀ ≫ SubalgebraStages.specHom S i₀) ⁻¹' s = Set.univ
    rw [SubalgebraStages.specLeg_specHom]
    exact H
  obtain ⟨j, f, hj⟩ := SchemeFiberGeometry.exists_map_preimage_eq_univ_of_isConstructible
    D c hc (op i₀) s₀ hs₀ hfull
  refine ⟨(S j.unop), j.unop.2.1, j.unop.2.2, ?_⟩
  change (SubalgebraStages.specHom S j.unop) ⁻¹' s = Set.univ
  change (SubalgebraStages.specTrans S f.unop.le ≫ SubalgebraStages.specHom S i₀) ⁻¹' s =
    Set.univ at hj
  rwa [SubalgebraStages.specTrans_specHom] at hj

open Langlands.Algebra.FiberMapEquality

/-- Finitely many coefficient enlargements suffice to retain equality on every
full residue-field tensor algebra. -/
theorem exists_fg_subalgebra_fiberMapEquality
    [IsNoetherianRing R₀]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]
    [Algebra.FiniteType R₀ A] [Algebra.FiniteType R₀ B]
    (f g : A →ₐ[R₀] B)
    (H : fiberMapEqualityLocus (baseChangeMap R f) (baseChangeMap R g) = Set.univ)
    (t : Finset R) :
    ∃ T : Subalgebra R₀ R, T.FG ∧ (↑t : Set R) ⊆ T ∧
      fiberMapEqualityLocus (baseChangeMap T f) (baseChangeMap T g) = Set.univ := by
  rw [fiberMapEqualityLocus_baseChange] at H
  obtain ⟨T, hT, ht, hfull⟩ := exists_fg_subalgebra_preimage_eq_univ
    (fiberMapEqualityLocus f g) (isConstructible_fiberMapEqualityLocus f g) H t
  exact ⟨T, hT, ht, (fiberMapEqualityLocus_baseChange f g).trans hfull⟩

/-- An actual finite coefficient algebra with every residue-fibre equation,
retaining any prescribed finite coefficient set. -/
structure FiberEqualityCoefficientModel
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]
    (f g : A →ₐ[R₀] B) (t : Finset R) where
  coefficients : Subalgebra R₀ R
  finiteGeneration : coefficients.FG
  contains : (↑t : Set R) ⊆ coefficients
  fiberEquality : fiberMapEqualityLocus (baseChangeMap coefficients f)
    (baseChangeMap coefficients g) = Set.univ

/-- Choose the coefficient model supplied by constructible-set detection at
the actual affine limit. -/
def fiberEqualityCoefficientModel
    [IsNoetherianRing R₀]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]
    [Algebra.FiniteType R₀ A] [Algebra.FiniteType R₀ B]
    (f g : A →ₐ[R₀] B)
    (H : fiberMapEqualityLocus (baseChangeMap R f) (baseChangeMap R g) = Set.univ)
    (t : Finset R) : FiberEqualityCoefficientModel f g t := by
  let h := exists_fg_subalgebra_fiberMapEquality f g H t
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2⟩

end Langlands.AlgebraicGeometry.FiberMapEqualityDescent
