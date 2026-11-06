import Langlands.Weil.Representation.InductionDual
import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.VirtualRepresentation.ExactDual

/-!
# Contragredients, restriction and induction on the exact quotient

The actual finite-index dual-induction equivalence gives the identity on
the continuous exact virtual group, without a semisimplicity hypothesis.
-/

noncomputable section

universe uG uH uV

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Restriction commutes with the actual contragredient on continuous
exact virtual representations. -/
theorem continuousRestrict_continuousDual (φ : H →ₜ* G)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousRestrict φ (continuousDual x) =
      continuousDual (continuousRestrict φ x) := by
  have h :
      (continuousRestrict.{uG, uH, uV} φ).comp
          (continuousDual.{uG, uV} (G := G)).toLinearMap =
        (continuousDual.{uH, uV} (G := H)).toLinearMap.comp
          (continuousRestrict.{uG, uH, uV} φ) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change restrict _ _ _ _ (dual _ _ (ofRepresentation _ A)) =
        dual _ _ (restrict _ _ _ _ (ofRepresentation _ A))
      rw [dual_ofRepresentation, restrict_ofRepresentation,
        restrict_ofRepresentation, dual_ofRepresentation]
      apply ofRepresentation_eq_of_equiv _
      change Representation.Equiv (A.val.representation.dual.comp φ.toMonoidHom)
        (Representation.dual (A.val.representation.comp φ.toMonoidHom))
      refine { toLinearEquiv := LinearEquiv.refl ℂ _, isIntertwining' := ?_ }
      intro g
      ext f v
      change f (A.val.representation ((φ g)⁻¹) v) =
        f (A.val.representation (φ g⁻¹) v)
      rw [map_inv φ g]
  exact LinearMap.congr_fun h x

/-- Contragredients commute with the existing actual exact induction
from an open finite-index subgroup. -/
theorem continuousDual_induce (S : Subgroup G) [S.FiniteIndex]
    (hS : IsOpen (S : Set G))
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ S => A.IsContinuous)) :
    continuousDual
        (induce S _ _ (fun _ hA =>
          FiniteRepresentation.isContinuous_induce S hS hA) x) =
      induce S _ _ (fun _ hA =>
        FiniteRepresentation.isContinuous_induce S hS hA) (continuousDual x) := by
  have h :
      (continuousDual.{uG, max uG uV} (G := G)).toLinearMap.comp
          (induce S _ _ (fun _ hA =>
            FiniteRepresentation.isContinuous_induce S hS hA)) =
        (induce S _ _ (fun _ hA =>
          FiniteRepresentation.isContinuous_induce S hS hA)).comp
            (continuousDual.{uG, uV} (G := S)).toLinearMap := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change dual _ _ (induce S _ _ _ (ofRepresentation _ A)) =
        induce S _ _ _ (dual _ _ (ofRepresentation _ A))
      rw [induce_ofRepresentation, dual_ofRepresentation,
        dual_ofRepresentation, induce_ofRepresentation]
      exact ofRepresentation_eq_of_equiv _
        (FiniteRepresentation.induceDualEquiv S A.val).symm
  exact LinearMap.congr_fun h x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
