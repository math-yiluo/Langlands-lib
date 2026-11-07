import Langlands.GroupScheme.MatrixRepresentation.FrobeniusDistributionAlgebra
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-! # The actual Frobenius-origin quotient as a Hopf algebra -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusHopfAlgebra

open FrobeniusCoordinateModel FrobeniusDistributionAlgebra TorusUnipotence

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [IsAffineHom G.X.hom]

local notation "C" => CharacterUnits.Coord G

/-- The algebra homomorphism classifying the inverse of the actual universal point. -/
def coordinateInverse : C →ₐ[k] C :=
  (Lie.pointCoordinates G) ((pt G (AlgHom.id k C))⁻¹)

@[simp]
theorem pt_coordinateInverse :
    pt G (coordinateInverse G) = (pt G (AlgHom.id k C))⁻¹ :=
  (Lie.pointCoordinates G).symm_apply_apply _

/-- Every algebra-valued point sends the coordinate inverse to group inversion. -/
theorem pt_comp_coordinateInverse {A : Type u} [CommRing A] [Algebra k A]
    (f : C →ₐ[k] A) :
    pt G (f.comp (coordinateInverse G)) = (pt G f)⁻¹ := by
  rw [pt_comp, pt_coordinateInverse, map_inv]
  congr 1
  simpa using (pt_comp G (AlgHom.id k C) f).symm

@[simp]
theorem coordinateInverse_comp_self :
    (coordinateInverse G).comp (coordinateInverse G) = AlgHom.id k C := by
  apply pt_injective G
  rw [pt_comp_coordinateInverse, pt_coordinateInverse, inv_inv]

@[simp]
theorem origin_comp_coordinateInverse :
    (Lie.coordinateOrigin G).comp (coordinateInverse G) = Lie.coordinateOrigin G := by
  apply pt_injective G
  rw [pt_comp_coordinateInverse]
  simp only [pt, Lie.coordinateOrigin, Equiv.symm_apply_apply, inv_one]

local instance coordinateBialgebra : Bialgebra k C := TorusUnipotence.coordBialgebra G

/-- Group inversion is an antipode for the original coordinate coproduct. -/
abbrev coordinateHopfAlgebra : HopfAlgebra k C :=
  HopfAlgebra.ofAlgHom (coordinateInverse G)
    (by
      change (Algebra.TensorProduct.productMap (coordinateInverse G) (AlgHom.id k C)).comp
          (CharacterUnits.comul G) =
        (Algebra.ofId k C).comp (Lie.coordinateOrigin G)
      apply pt_injective G
      rw [pt_comp_comul G _ (Algebra.TensorProduct.productMap_left _ _)
          (Algebra.TensorProduct.productMap_right _ _),
        pt_coordinateInverse, inv_mul_cancel, pt_comp_coordinateOrigin])
    (by
      change (Algebra.TensorProduct.productMap (AlgHom.id k C) (coordinateInverse G)).comp
          (CharacterUnits.comul G) =
        (Algebra.ofId k C).comp (Lie.coordinateOrigin G)
      apply pt_injective G
      rw [pt_comp_comul G _ (Algebra.TensorProduct.productMap_left _ _)
          (Algebra.TensorProduct.productMap_right _ _),
        pt_coordinateInverse, mul_inv_cancel, pt_comp_coordinateOrigin])

local instance : HopfAlgebra k C := coordinateHopfAlgebra G

variable (p : ℕ) [ExpChar k p] (r : ℕ)

/-- Inversion preserves the actual Frobenius augmentation ideal. -/
theorem inverse_mem_quotientIdeal {a : C} (ha : a ∈ quotientIdeal G p r) :
    coordinateInverse G a ∈ quotientIdeal G p r := by
  have hle : quotientIdeal G p r ≤ (quotientIdeal G p r).comap (coordinateInverse G) := by
    rw [quotientIdeal, Ideal.map_le_iff_le_comap]
    intro a ha
    change coordinateInverse G (a ^ p ^ r) ∈ quotientIdeal G p r
    rw [map_pow]
    apply Ideal.mem_map_of_mem
    change Lie.coordinateOrigin G (coordinateInverse G a) = 0
    have h := AlgHom.congr_fun (origin_comp_coordinateInverse G) a
    exact h.trans ha
  exact hle ha

local instance quotientHopfIdeal : (quotientIdeal G p r).IsHopfIdeal k where
  toIsCoideal := quotientIdeal_isCoideal G p r
  antipode_mem := by
    intro a ha
    exact inverse_mem_quotientIdeal G p r ha

/-- The quotient retains the Hopf structure of the actual group. -/
instance quotientHopfAlgebra : HopfAlgebra k (quotientAlgebra G p r) :=
  inferInstanceAs (HopfAlgebra k (C ⧸ quotientIdeal G p r))

@[simp]
theorem antipode_quotientMap (a : C) :
    HopfAlgebra.antipode k (quotientMap G p r a) =
      quotientMap G p r (coordinateInverse G a) := rfl

/-- The quotient antipode is involutive because actual group inversion is. -/
theorem antipode_involutive :
    Function.Involutive (HopfAlgebra.antipode k (A := quotientAlgebra G p r)) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (quotientIdeal G p r) x
  change quotientMap G p r (coordinateInverse G (coordinateInverse G a)) =
    quotientMap G p r a
  exact congrArg (quotientMap G p r) (AlgHom.congr_fun (coordinateInverse_comp_self G) a)

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusHopfAlgebra
