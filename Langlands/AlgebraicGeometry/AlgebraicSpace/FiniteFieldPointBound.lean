import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # A bound on field-valued points of a finite morphism over a point -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- For a finite morphism `p : R ⟶ U` and a point `η` of `U`, the number of distinct
`K`-valued points of `R` over a fixed `K`-valued point of `U` at `η` is bounded independently of
the field `K`. -/
theorem exists_card_le_of_isFinite {R U : Scheme.{u}} (p : R ⟶ U) [IsFinite p] (η : U) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (α : U.residueField η ⟶ CommRingCat.of K) (m : ℕ)
      (r : Fin m → (Spec (CommRingCat.of K) ⟶ R)), Function.Injective r →
        (∀ j, r j ≫ p = Spec.map α ≫ U.fromSpecResidueField η) → m ≤ N := by
  let F := p.fiber η
  let π : F ⟶ Spec (U.residueField η) := p.fiberToSpecResidueField η
  have : IsFinite π :=
    MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback p (U.fromSpecResidueField η)) ‹_›
  have : IsAffine F := isAffine_of_isAffineHom π
  let φ : U.residueField η ⟶ Γ(F, ⊤) := (Scheme.ΓSpecIso (U.residueField η)).inv ≫ π.appTop
  let : Algebra (U.residueField η) Γ(F, ⊤) := φ.hom.toAlgebra
  have : Module.Finite (U.residueField η) Γ(F, ⊤) := by
    have h1 : π.appTop.hom.Finite := π.finite_appTop
    have h2 : (Scheme.ΓSpecIso (U.residueField η)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact (h1.comp h2 : (π.appTop.hom.comp (Scheme.ΓSpecIso (U.residueField η)).inv.hom).Finite)
  refine ⟨Module.finrank (U.residueField η) Γ(F, ⊤), ?_⟩
  intro K _ α m r hr hrp
  let : Algebra (U.residueField η) K := α.hom.toAlgebra
  let s : Fin m → (Spec (CommRingCat.of K) ⟶ F) := fun j =>
    pullback.lift (r j) (Spec.map α) (hrp j)
  have hs : ∀ j, s j ≫ p.fiberι η = r j := fun j => pullback.lift_fst _ _ _
  have hsπ : ∀ j, s j ≫ π = Spec.map α := fun j => pullback.lift_snd _ _ _
  let ψ : Fin m → (Γ(F, ⊤) ⟶ CommRingCat.of K) := fun j =>
    (s j).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hψ : ∀ j, φ ≫ ψ j = α := by
    intro j
    simp only [φ, ψ, Category.assoc]
    rw [← Category.assoc π.appTop, ← Scheme.Hom.comp_appTop, hsπ j,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  let ψa : Fin m → (Γ(F, ⊤) →ₐ[U.residueField η] K) := fun j =>
    { (ψ j).hom with
      commutes' := fun a => by
        change (ψ j).hom (φ.hom a) = α.hom a
        rw [← CommRingCat.comp_apply, hψ j] }
  have hψa : Function.Injective ψa := by
    intro j k hjk
    apply hr
    have h1 : ψ j = ψ k := by
      ext x
      exact congrArg (fun g : Γ(F, ⊤) →ₐ[U.residueField η] K => g x) hjk
    have h2 : (s j).appTop = (s k).appTop := by
      simpa [ψ] using h1
    rw [← hs j, ← hs k, ext_of_isAffine h2]
  calc m = Nat.card (Fin m) := (Nat.card_fin m).symm
    _ ≤ Nat.card (Γ(F, ⊤) →ₐ[U.residueField η] K) := Nat.card_le_card_of_injective _ hψa
    _ ≤ Module.finrank (U.residueField η) Γ(F, ⊤) := card_algHom_le_finrank _ _ _

end Langlands.AlgebraicGeometry.AlgebraicSpace
