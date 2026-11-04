import Langlands.GroupScheme.Torus.CocycleModelActionRelationSmoothStatement
import Langlands.GroupScheme.Torus.CocycleConjugacyLifting
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.AlgebraicGeometry.AffineLiftingSmooth

/-! # Smooth action relations on diagonalizable cocycle models: proof -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.Diagonalizable

/-- **Smoothness of the action relation** (Conrad–Gabber–Prasad, proof of Proposition A.8.12,
using A.8.10(2)). For a diagonalizable action on a smooth affine group over a field, the map
`(g, x) ↦ (g · x, x)` on any affine finite-type cocycle model is smooth. -/
theorem cocycleModelActionRelationSmooth : CocycleModelActionRelationSmoothStatement.{u} := by
  intro k _ Λ _ _ G _ _ a M _ _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine M.scheme.left := isAffine_of_isAffineHom M.scheme.hom
  have : Algebra.Smooth (CommRingCat.of k) (AffineCoordinates.algebra G) :=
    AffineCoordinates.smooth_algebra G inferInstance
  have : IsAffine (G.X ⊗ M.scheme).left := by
    change IsAffine (CategoryTheory.Limits.pullback G.X.hom M.scheme.hom)
    infer_instance
  have : IsAffine (M.scheme ⊗ M.scheme).left := by
    change IsAffine (CategoryTheory.Limits.pullback M.scheme.hom M.scheme.hom)
    infer_instance
  have : LocallyOfFiniteType (G.X ⊗ M.scheme).hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.fst G.X.hom M.scheme.hom ≫ G.X.hom)
    infer_instance
  have : IsLocallyNoetherian M.scheme.left := LocallyOfFiniteType.isLocallyNoetherian M.scheme.hom
  have : IsLocallyNoetherian (M.scheme ⊗ M.scheme).left := by
    change IsLocallyNoetherian (CategoryTheory.Limits.pullback M.scheme.hom M.scheme.hom)
    infer_instance
  have : LocallyOfFiniteType M.actionRelation.left := by
    have : LocallyOfFiniteType (M.actionRelation.left ≫ (M.scheme ⊗ M.scheme).hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (M.scheme ⊗ M.scheme).hom
  apply AlgebraicGeometry.AffineLifting.smooth_of_lifting
  intro C I hI y x₀ hsq
  let π := (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ _ I)).op
  let g₀ := x₀ ≫ fst G.X M.scheme
  let m₀ := x₀ ≫ snd G.X M.scheme
  let yy := y ≫ fst M.scheme M.scheme
  let xx := y ≫ snd M.scheme M.scheme
  have hx₀ : x₀ = CartesianMonoidalCategory.lift g₀ m₀ := by
    simp only [g₀, m₀]
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have hrel : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (m : T ⟶ M.scheme),
      CartesianMonoidalCategory.lift g m ≫ M.actionRelation =
        CartesianMonoidalCategory.lift (M.action.act g m) m := by
    intro T g m
    rw [AutomorphicAction.CocycleModel.actionRelation, comp_lift, lift_snd]
    rfl
  rw [hx₀, hrel] at hsq
  have hfst : M.action.act g₀ m₀ = π ≫ yy := by
    have := congrArg (· ≫ fst M.scheme M.scheme) hsq
    simpa [yy] using this
  have hsnd : m₀ = π ≫ xx := by
    have := congrArg (· ≫ snd M.scheme M.scheme) hsq
    simpa [xx] using this
  have hg₀ : AutomorphicAction.Cocycle.conjugate g₀
      (AutomorphicAction.Cocycle.restrict π (M.cocycle xx)) =
        AutomorphicAction.Cocycle.restrict π (M.cocycle yy) := by
    rw [M.restrict_cocycle, M.restrict_cocycle, ← hsnd, ← hfst, M.cocycle_act]
  have hnil : IsNilpotent I := ⟨2, by rw [hI]; rfl⟩
  obtain ⟨g, hgred, hg⟩ := CharacterAction.exists_conjugate_lift a (M.cocycle xx) (M.cocycle yy)
    I hnil g₀ hg₀
  have hact : M.action.act g xx = yy := by
    apply M.cocycle_injective
    rw [M.cocycle_act, hg]
  refine ⟨CartesianMonoidalCategory.lift g xx, ?_, ?_⟩
  · rw [hrel, hact]
    simp [yy, xx]
  · rw [comp_lift, hgred, ← hsnd, hx₀]

end Langlands.GroupScheme.Diagonalizable
