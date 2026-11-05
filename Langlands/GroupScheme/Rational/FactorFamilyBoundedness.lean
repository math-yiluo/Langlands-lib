import Langlands.GroupScheme.MatrixRepresentation.FactorSum
import Langlands.GroupScheme.Rational.SpectralFamilyBound
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegralityOn
import Langlands.AlgebraicGeometry.PointTopology.AffineFiniteBoundedness

/-! # Boundedness from the spans of the actual simple factors -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.SimpleFactorFamily

variable {k : Type u} [Field k] [ValuativeRel k]
  {G : GroupScheme (Spec (CommRingCat.of k))} {N M : ℕ}
  {ρ : MatrixRepresentation G (Fin N)} {τ : MatrixRepresentation G (Fin M)}
  {I : Type v} [Monoid I] (F : SimpleFactorFamily ρ τ)

/-- Each chosen simple factor has full matrix span on the specified monoid family. -/
def HasFullMatrixSpans (α : I →* rationalPoints G) : Prop :=
  ∀ i, Submodule.span k (Set.range fun a =>
    ((F.factor i).rationalMatrix (α a) :
      Matrix (Fin (F.dimension i)) (Fin (F.dimension i)) k)) = ⊤

/-- Integral characteristic coefficients of the original representation bound
the actual factor sum on any monoid family spanning in each simple factor. -/
theorem hasBoundedRationalEntries_factorSum
    (α : I →* rationalPoints G) (hspan : F.HasFullMatrixSpans α)
    (hint : ∀ a d, (ρ.rationalMatrix (α a) :
      Matrix (Fin N) (Fin N) k).charpoly.coeff d ≤ᵥ (1 : k)) :
    F.factorSum.HasBoundedRationalEntries (Set.range α) := by
  apply hasBoundedRationalEntries_directSum F.factor (Set.range α)
  intro i
  apply (F.factor i).hasBoundedRationalEntries_range_of_span α (hspan i)
  intro a
  exact (F.subquotient i).charpoly_coeff_vle_one (α a) (hint a)

section Finiteness

variable [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {I : Type v} [Group I] {ρ : MatrixRepresentation G (Fin N)}
  (F : SimpleFactorFamily ρ ρ)

local instance factorFamilyBoundednessInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- For a reductive-type source with a closed faithful original action, full
matrix span in the simple factors and coefficient bounds on a subgroup family
bound every regular function on that same family of actual rational points. -/
theorem isAlgebraicallyBounded_range_of_fullMatrixSpans
    (hG : HasTrivialUnipotentRadical G) (hc : IsClosedSubgroup ρ)
    (α : I →* rationalPoints G) (hspan : F.HasFullMatrixSpans α)
    (hint : ∀ a d, (ρ.rationalMatrix (α a) :
      Matrix (Fin N) (Fin N) k).charpoly.coeff d ≤ᵥ (1 : k)) :
    IsAlgebraicallyBounded k G.X (Set.range α) := by
  let : IsFinite F.factorSum.hom.hom.left := F.isFinite_factorSum hG hc
  let : IsAffine (GeneralLinear.groupScheme
      (Σ i : Fin F.length, Fin (F.dimension i)) (CommRingCat.of k)).X.left :=
    GeneralLinear.isAffine_groupScheme _ _
  apply isAlgebraicallyBounded_of_integralHom k F.factorSum.hom.hom (Set.range α)
  apply F.factorSum.isAlgebraicallyBounded_image_of_entries (Set.range α)
  · rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, map_inv α a⟩
  · exact F.hasBoundedRationalEntries_factorSum α hspan hint

end Finiteness

end Langlands.GroupScheme.MatrixRepresentation.SimpleFactorFamily
