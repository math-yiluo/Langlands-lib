import Langlands.Representation.Twist.Coinduction
import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.VirtualRepresentation.ExactTwist

/-!
# Character twisting and induction on continuous exact virtual groups

The actual equivariant-function equivalence descends to the quotient by
all short exact relations.
-/

noncomputable section

universe uK uG uH uV

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- Scalar twisting commutes with the existing actual finite-index
equivariant-function induction. -/
def induceTwistEquiv (S : Subgroup G) [S.FiniteIndex] (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K S) :
    Equiv (induce S (twist (χ.comp S.subtype) A)) (twist χ (induce S A)) :=
  Langlands.coindTwistEquiv S.subtype χ A.representation

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Continuous restriction commutes with actual continuous-character twisting. -/
theorem continuousRestrict_continuousTwist (φ : H →ₜ* G) (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousRestrict φ (continuousTwist χ x) =
      continuousTwist (χ.comp φ) (continuousRestrict φ x) := by
  have h :
      (continuousRestrict φ).comp (continuousTwist χ).toLinearMap =
        (continuousTwist (χ.comp φ)).toLinearMap.comp (continuousRestrict φ) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change restrict _ _ _ _ (twist _ _ _ _ (ofRepresentation _ A)) =
        twist _ _ _ _ (restrict _ _ _ _ (ofRepresentation _ A))
      rw [twist_ofRepresentation, restrict_ofRepresentation,
        restrict_ofRepresentation, twist_ofRepresentation]
      exact ofRepresentation_eq_of_equiv _ (Representation.Equiv.refl _)
  exact LinearMap.congr_fun h x

variable [IsTopologicalGroup G]

/-- Finite-index induction on the exact virtual group of ordinary
continuous representations of an open subgroup. -/
def continuousInduce (S : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G)) :
    ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ S => A.IsContinuous) →ₗ[ℤ]
      ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G => A.IsContinuous) :=
  induce S _ _ (fun _ hA => FiniteRepresentation.isContinuous_induce S hS hA)

/-- The projection formula for a continuous scalar character on the actual
exact virtual quotient. -/
theorem continuousInduce_continuousTwist (S : Subgroup G) [S.FiniteIndex]
    (hS : IsOpen (S : Set G)) (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ S => A.IsContinuous)) :
    continuousInduce S hS
        (continuousTwist
          (χ.comp ⟨S.subtype, continuous_subtype_val⟩) x) =
      continuousTwist χ (continuousInduce S hS x) := by
  have h :
      (continuousInduce S hS).comp
          (continuousTwist (χ.comp ⟨S.subtype, continuous_subtype_val⟩)).toLinearMap =
        (continuousTwist χ).toLinearMap.comp (continuousInduce S hS) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change induce S _ _ _ (twist _ _ _ _ (ofRepresentation _ A)) =
        twist _ _ _ _ (induce S _ _ _ (ofRepresentation _ A))
      rw [twist_ofRepresentation, induce_ofRepresentation,
        induce_ofRepresentation, twist_ofRepresentation]
      exact ofRepresentation_eq_of_equiv _
        (FiniteRepresentation.induceTwistEquiv S χ.toMonoidHom A.val)
  exact LinearMap.congr_fun h x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
