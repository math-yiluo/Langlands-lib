import Langlands.GroupScheme.Rational.TorusUnipotence.StandardUnipotentAction
import Langlands.GroupScheme.Rational.TorusUnipotence.LieWeightMultiplicity
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusTopIntegral

/-! # Polynomial coordinates and Frobenius quotients of actual dynamic unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Standard

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (hT : IsSplitTorus T.toGrp)
    [Smooth G.X.hom]

local notation "U" => unipotentScheme i ν ∅

/-- Polynomial eigen-coordinates on the actual representative of `U_G(ν)`.
The algebra coordinates do not identify the group law with addition. -/
structure UnipotentPolynomialCoordinates where
  dimension : ℕ
  weight : Fin dimension → characterLattice T
  generator : Fin dimension → CharacterUnits.Coord U
  bijective : Function.Bijective
    (aeval generator : MvPolynomial (Fin dimension) k →ₐ[k] CharacterUnits.Coord U)
  homogeneous : ∀ j, generator j ∈
    CoordinateWeights.weightSpace (unipotentAction i ν hT) (weight j)
  origin_zero : ∀ j, TorusUnipotence.coordCounit U (generator j) = 0
  positive : ∀ j, 0 < latticePairing T (weight j) ν
  monotone_height : Monotone (fun j => latticePairing T (weight j) ν)

/-- Smooth dynamic unipotent groups have pointed polynomial eigen-coordinates,
constructed from the published positivity of their actual augmentation weights. -/
def unipotentPolynomialCoordinates : UnipotentPolynomialCoordinates i ν hT := by
  classical
  have : Smooth (unipotentScheme i ν ∅).X.hom :=
    smooth_unipotentScheme_empty i ν hT
  have hex : Nonempty (UnipotentPolynomialCoordinates i ν hT) := by
    obtain ⟨d, w, t, ht, htw, hε, hw, hmono⟩ :=
      TorusUnipotence.exists_positiveWeight_coordinates hT (unipotentAction i ν hT) ν
        (fun _ hχ => pairing_pos_of_mem_support i ν hT hχ)
    exact ⟨⟨d, w, t, ht, htw, hε, hw, hmono⟩⟩
  exact Classical.choice hex

namespace UnipotentPolynomialCoordinates

variable {i ν hT}

variable (coords : UnipotentPolynomialCoordinates i ν hT)

/-- The algebra equivalence furnished by the constructed eigenfunctions. -/
def polynomialEquiv :
    CharacterUnits.Coord U ≃ₐ[k] MvPolynomial (Fin coords.dimension) k :=
  MatrixRepresentation.FrobeniusTopIntegral.polynomialCoordinates coords.generator coords.bijective

theorem polynomialEquiv_origin (a : CharacterUnits.Coord U) :
    (coords.polynomialEquiv a).coeff 0 = Lie.coordinateOrigin U a :=
  MatrixRepresentation.FrobeniusTopIntegral.polynomialCoordinates_origin
    coords.generator coords.bijective coords.origin_zero a

/-- The number of polynomial generators is the dimension of the actual Lie kernel. -/
theorem dimension_eq_finrank_lie :
    coords.dimension = Module.finrank k (Additive (lieKernel U k)) := by
  have h := (TorusUnipotence.tangentCoordinatesEquiv coords.bijective coords.origin_zero).finrank_eq
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h.symm

open MatrixRepresentation.FrobeniusCoordinateModel
open MatrixRepresentation.FrobeniusPolynomialBox
open Langlands.Algebra.PolynomialBoxQuotient

variable (p : ℕ) [ExpChar k p] (r : ℕ)

include coords in
/-- The exact Frobenius augmentation quotient of the actual dynamic subgroup
is finite dimensional, with no further coordinate-existence premise. -/
theorem finite_frobeniusQuotient : Module.Finite k (quotientAlgebra U p r) :=
  finite_quotientAlgebra U p r coords.polynomialEquiv coords.polynomialEquiv_origin

theorem finrank_frobeniusQuotient :
    Module.finrank k (quotientAlgebra U p r) = (p ^ r) ^ coords.dimension :=
  finrank_quotientAlgebra U p r coords.polynomialEquiv coords.polynomialEquiv_origin

include coords in
/-- The quotient dimension is intrinsic to the actual Lie kernel. -/
theorem finrank_frobeniusQuotient_eq_lie :
    Module.finrank k (quotientAlgebra U p r) =
      (p ^ r) ^ Module.finrank k (Additive (lieKernel U k)) := by
  rw [coords.finrank_frobeniusQuotient p r, coords.dimension_eq_finrank_lie]

/-- Vanishing in the actual quotient is precisely vanishing of the retained
polynomial coefficients, with the same Frobenius height. -/
theorem quotientMap_eq_zero_iff (a : CharacterUnits.Coord U) :
    quotientMap U p r a = 0 ↔
      ∀ m : Fin coords.dimension →₀ ℕ, m ≤ bound p coords.dimension r →
        (coords.polynomialEquiv a).coeff m = 0 := by
  change Ideal.Quotient.mk (quotientIdeal U p r) a = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hm : a ∈ quotientIdeal U p r ↔
      coords.polynomialEquiv a ∈ boxIdeal (bound p coords.dimension r) := by
    rw [← map_quotientIdeal U p r coords.polynomialEquiv coords.polynomialEquiv_origin,
      Ideal.mem_map_iff_of_surjective coords.polynomialEquiv.toRingHom
        coords.polynomialEquiv.surjective]
    exact ⟨fun ha => ⟨a, ha, rfl⟩, fun ⟨b, hb, he⟩ =>
      coords.polynomialEquiv.injective he ▸ hb⟩
  rw [hm, mem_boxIdeal]

end UnipotentPolynomialCoordinates

end Langlands.GroupScheme.Standard
