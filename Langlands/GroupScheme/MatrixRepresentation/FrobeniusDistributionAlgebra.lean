import Langlands.GroupScheme.MatrixRepresentation.FrobeniusOriginUniversality
import Langlands.GroupScheme.Rational.TorusUnipotence.MatrixCoefficients
import Mathlib.RingTheory.Bialgebra.Quotient

/-! # Bialgebra of the actual Frobenius-origin quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusDistributionAlgebra

open FrobeniusCoordinateModel FrobeniusOrderedDistributions FrobeniusOriginUniversality

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (.of k))) [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

local notation "C" => CharacterUnits.Coord G
local notation "Q" => quotientAlgebra G p r

local instance coordinateBialgebra : Bialgebra k C := TorusUnipotence.coordBialgebra G

/-- The actual identity evaluation kills the defining Frobenius ideal. -/
theorem quotientIdeal_le_ker_origin :
    quotientIdeal G p r ≤ RingHom.ker (Lie.coordinateOrigin G).toRingHom := by
  rw [quotientIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change Lie.coordinateOrigin G (a ^ p ^ r) = 0
  change Lie.coordinateOrigin G a = 0 at ha
  rw [map_pow, ha, zero_pow (pow_ne_zero _ (expChar_ne_zero k p))]

/-- Applying both identity evaluations to the true coordinate coproduct is
again the identity evaluation. -/
theorem product_origin_comul (a : C) :
    Algebra.TensorProduct.productMap (Lie.coordinateOrigin G) (Lie.coordinateOrigin G)
      (CharacterUnits.comul G a) = Lie.coordinateOrigin G a := by
  have h : (Algebra.TensorProduct.productMap (Lie.coordinateOrigin G)
      (Lie.coordinateOrigin G)).comp (CharacterUnits.comul G) = Lie.coordinateOrigin G := by
    apply TorusUnipotence.pt_injective G
    rw [TorusUnipotence.pt_comp_comul G _
      (Algebra.TensorProduct.productMap_left _ _)
      (Algebra.TensorProduct.productMap_right _ _)]
    simp only [TorusUnipotence.pt, Lie.coordinateOrigin, Equiv.symm_apply_apply, one_mul]
  exact AlgHom.congr_fun h a

/-- On the tensor of the two actual quotients, the characteristic power of
any original tensor coordinate is its identity value's characteristic power. -/
theorem tensor_quotient_pow (z : C ⊗[k] C) :
    Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r) z ^ p ^ r =
      algebraMap k (Q ⊗[k] Q)
        ((Algebra.TensorProduct.productMap (Lie.coordinateOrigin G)
          (Lie.coordinateOrigin G) z) ^ p ^ r) := by
  let F := characteristicPowerMap k p (Q ⊗[k] Q) r
  let Fk := characteristicPowerMap k p k r
  change F (Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r) z) =
    algebraMap k (Q ⊗[k] Q)
      (Fk (Algebra.TensorProduct.productMap (Lie.coordinateOrigin G) (Lie.coordinateOrigin G) z))
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)
      (a ⊗ₜ[k] b)) ^ p ^ r = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow,
      quotient_pow_origin, quotient_pow_origin]
    change ((algebraMap k Q (Lie.coordinateOrigin G a)) ^ p ^ r) ⊗ₜ[k]
      ((algebraMap k Q (Lie.coordinateOrigin G b)) ^ p ^ r) =
      algebraMap k (Q ⊗[k] Q)
        ((Algebra.TensorProduct.productMap (Lie.coordinateOrigin G)
          (Lie.coordinateOrigin G) (a ⊗ₜ[k] b)) ^ p ^ r)
    simp only [← map_pow, Algebra.TensorProduct.productMap_apply_tmul, mul_pow, map_mul]
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, Algebra.TensorProduct.one_def, smul_smul]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add, map_add]

/-- The Frobenius augmentation ideal is a coideal for the original group
coproduct, so its quotient inherits the original multiplication law. -/
theorem quotientIdeal_isCoideal :
    ((quotientIdeal G p r).restrictScalars k).IsCoideal := by
  constructor
  · intro a ha
    exact quotientIdeal_le_ker_origin G p r ha
  · intro a ha
    change Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)
      (CharacterUnits.comul G a) = 0
    have hle : quotientIdeal G p r ≤ RingHom.ker
        (((Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)).comp
          (CharacterUnits.comul G)).toRingHom) := by
      rw [quotientIdeal, Ideal.map_le_iff_le_comap]
      intro b hb
      change Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)
        (CharacterUnits.comul G (b ^ p ^ r)) = 0
      rw [map_pow, map_pow, tensor_quotient_pow, product_origin_comul]
      change Lie.coordinateOrigin G b = 0 at hb
      rw [hb, zero_pow (pow_ne_zero _ (expChar_ne_zero k p)), map_zero]
    exact hle ha

local instance quotientCoideal :
    ((quotientIdeal G p r).restrictScalars k).IsCoideal := quotientIdeal_isCoideal G p r

/-- The canonical bialgebra structure of the actual Frobenius-origin quotient. -/
instance quotientBialgebra : Bialgebra k Q :=
  inferInstanceAs (Bialgebra k (C ⧸ quotientIdeal G p r))

@[simp]
theorem counit_quotientMap (a : C) :
    Coalgebra.counit (R := k) (quotientMap G p r a) = Lie.coordinateOrigin G a := rfl

@[simp]
theorem comul_quotientMap (a : C) :
    Coalgebra.comul (R := k) (quotientMap G p r a) =
      Algebra.TensorProduct.map (quotientMap G p r) (quotientMap G p r)
        (CharacterUnits.comul G a) := rfl

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusDistributionAlgebra
