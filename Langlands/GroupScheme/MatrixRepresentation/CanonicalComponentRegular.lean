import Langlands.GroupScheme.MatrixRepresentation.FiniteComponentQuotientRegular
import Langlands.GroupScheme.ComponentPointQuotient

/-! # The canonical rational component regular representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.ComponentConstant

namespace Langlands.GroupScheme.MatrixRepresentation

open IdentityComponent

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The canonical rational quotient is constant on actual connected components. -/
theorem componentPointProjection_constant
    (x y : rationalPoints G)
    (hxy : sectionComponent G.X x = sectionComponent G.X y) :
    componentPointProjection G x = componentPointProjection G y := by
  apply (componentPointEmbedding G).injective
  change pointComponent G x = pointComponent G y
  exact hxy

section AlgebraicallyClosed

variable [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- The canonical finite rational component quotient has an actual regular
representation in a chosen finite coordinate dimension. -/
def componentRegularRepresentation : Σ n : ℕ, MatrixRepresentation G (Fin n) := by
  letI := Fintype.ofFinite (ComponentPointQuotient G)
  exact ⟨Fintype.card (ComponentPointQuotient G),
    finiteComponentQuotientRegular G (componentPointProjection G)
      (componentPointProjection_constant G)⟩

/-- Over an algebraically closed field, linear reductivity forces the canonical
rational component quotient to have order prime to the characteristic. -/
theorem not_dvd_card_componentPointQuotient_of_linearlyReductive
    (p : ℕ) [CharP k p]
    (hLR : ∀ n (ρ : MatrixRepresentation G (Fin n)), ρ.IsSemisimple) :
    ¬ p ∣ Nat.card (ComponentPointQuotient G) := by
  let := Fintype.ofFinite (ComponentPointQuotient G)
  exact not_dvd_card_of_linearlyReductive_finiteComponentQuotient G
    (componentPointProjection G) (componentPointProjection_surjective G)
    (componentPointProjection_constant G) p hLR

/-- The same order obstruction in terms of the actual scheme's connected
components over an algebraically closed field. -/
theorem not_dvd_card_connectedComponents_of_linearlyReductive
    (p : ℕ) [CharP k p]
    (hLR : ∀ n (ρ : MatrixRepresentation G (Fin n)), ρ.IsSemisimple) :
    ¬ p ∣ Nat.card (_root_.ConnectedComponents G.X.left) := by
  rw [← Nat.card_congr (componentPointQuotientEquiv G)]
  exact not_dvd_card_componentPointQuotient_of_linearlyReductive G p hLR

end AlgebraicallyClosed

section Geometric

variable [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- For an arbitrary base field, the geometric component-order obstruction
follows if linear reductivity is supplied after extension to the chosen algebraic
closure. This does not assert preservation under field extension. -/
theorem not_dvd_card_geometricComponents_of_baseChange_linearlyReductive
    (p : ℕ) [CharP k p]
    (hLR : ∀ n (ρ : MatrixRepresentation
      (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G) (Fin n)),
        ρ.IsSemisimple) :
    ¬ p ∣ Nat.card (GeometricComponents k G) := by
  let : LocallyOfFiniteType
      (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.snd G.X.hom (GaloisPointComparison.baseMap k (AlgebraicClosure k))))
  let : IsAffineHom
      (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G).X.hom :=
    inferInstanceAs (IsAffineHom
      (Limits.pullback.snd G.X.hom (GaloisPointComparison.baseMap k (AlgebraicClosure k))))
  rw [natCard_geometricComponents_eq_componentPointQuotient G]
  exact not_dvd_card_componentPointQuotient_of_linearlyReductive
    (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G) p hLR

end Geometric

end Langlands.GroupScheme.MatrixRepresentation
