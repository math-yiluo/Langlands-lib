import Langlands.GroupScheme.Torus.LocalDiagonalizableHomComparison
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Reparametrizing a clopen lift to match a prescribed fibre isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.PrescribedDiagonalizableLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- A clopen lift from any diagonalizable source can be reparametrized to
recover any prescribed diagonalization of the special fibre exactly. -/
theorem reparametrize_clopen_lift
    {A : Type u} [CommRing A] [IsLocalRing A]
    {C₀ C₁ H : GroupScheme (Spec (CommRingCat.of A))}
    (h₀ : RelativeMultiplicativeType.IsDiagonalizable C₀)
    (h₁ : RelativeMultiplicativeType.IsDiagonalizable C₁)
    (j₁ : C₁ ⟶ H)
    (hop : IsOpenImmersion j₁.hom.hom.left)
    (hcl : IsClosedImmersion j₁.hom.hom.left)
    [IsIso ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j₁)]
    (e₀ : (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj C₀ ≅
      (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H) :
    ∃ j₀ : C₀ ⟶ H,
      (baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j₀ = e₀.hom ∧
      IsOpenImmersion j₀.hom.hom.left ∧ IsClosedImmersion j₀.hom.hom.left := by
  let sp := Spec.algebraMap A (IsLocalRing.ResidueField A)
  obtain ⟨t, ht, -⟩ := CompleteLocalDeformation.diagonalizable_existsUnique_lift sp h₀ h₁
    (e₀.hom ≫ inv ((baseChange sp).map j₁))
  have : IsIso ((baseChange sp).map t) := by
    rw [ht]
    infer_instance
  have : IsIso t := CompleteLocalDeformation.diagonalizable_isIso_of_baseChange sp h₀ h₁ t
  refine ⟨t ≫ j₁, ?_, ?_, ?_⟩
  · change (baseChange sp).map (t ≫ j₁) = _
    rw [Functor.map_comp, ht, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · change IsOpenImmersion (t.hom.hom.left ≫ j₁.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  · change IsClosedImmersion (t.hom.hom.left ≫ j₁.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance

end Langlands.GroupScheme.PrescribedDiagonalizableLift
