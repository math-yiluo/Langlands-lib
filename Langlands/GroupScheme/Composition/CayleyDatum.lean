import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.StabilizerClosedSubgroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Actual eight-dimensional unital composition data and automorphism equations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The coordinate space of a Cayley algebra. -/
abbrev CayleyVector (R : Type u) := Fin 8 → R

/-- A unital bilinear multiplication with a nonsingular multiplicative quadratic
norm in dimension eight. Associativity is not assumed. -/
structure CayleyDatum (K : Type u) [Field K] where
  multiplication : CayleyVector K →ₗ[K] CayleyVector K →ₗ[K] CayleyVector K
  unit : CayleyVector K
  norm : QuadraticForm K (CayleyVector K)
  unit_mul : ∀ x, multiplication unit x = x
  mul_unit : ∀ x, multiplication x unit = x
  norm_unit : norm unit = 1
  norm_mul : ∀ x y, norm (multiplication x y) = norm x * norm y
  polar_nondegenerate : ∀ x, (∀ y, norm.polarBilin x y = 0) → x = 0

namespace CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

/-- The output coordinate `i` of the product of standard basis vectors `j` and `k`. -/
def structureConstant (i j k : Fin 8) : K :=
  c.multiplication (Pi.single j 1) (Pi.single k 1) i

/-- Multiplication after extension to any commutative coefficient algebra,
defined by the same structure constants. -/
def multiplicationOver {A : Type u} [CommRing A] (φ : K →+* A)
    (x y : CayleyVector A) : CayleyVector A :=
  fun i => ∑ j, ∑ k, φ (c.structureConstant i j k) * x j * y k

/-- The unit vector after extension of coefficients. -/
def unitOver {A : Type u} [CommRing A] (φ : K →+* A) : CayleyVector A :=
  fun i => φ (c.unit i)

theorem multiplication_apply_eq_sum (x y : CayleyVector K) (i : Fin 8) :
    c.multiplication x y i =
      ∑ j, ∑ k, c.structureConstant i j k * x j * y k := by
  have hx : x = ∑ j, x j • Pi.single j (1 : K) := by
    ext a
    simp [Pi.single_apply]
  have hy : y = ∑ k, y k • Pi.single k (1 : K) := by
    ext a
    simp [Pi.single_apply]
  conv_lhs => rw [hx, hy]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  dsimp [structureConstant]
  ring

/-- At the original field the coordinate extension is the given multiplication. -/
@[simp] theorem multiplicationOver_self (x y : CayleyVector K) :
    c.multiplicationOver (RingHom.id K) x y = c.multiplication x y := by
  ext i
  simpa [multiplicationOver] using (c.multiplication_apply_eq_sum x y i).symm

@[simp] theorem unitOver_self : c.unitOver (RingHom.id K) = c.unit := by
  ext i
  simp [unitOver]

/-- An invertible matrix fixes the extended unit and preserves the extended
bilinear multiplication. Matrices act on column vectors. -/
def IsAutomorphismMatrix {A : Type u} [CommRing A] (φ : K →+* A)
    (g : GL (Fin 8) A) : Prop :=
  (g : Matrix (Fin 8) (Fin 8) A).mulVec (c.unitOver φ) = c.unitOver φ ∧
    ∀ x y : CayleyVector A,
      (g : Matrix (Fin 8) (Fin 8) A).mulVec (c.multiplicationOver φ x y) =
        c.multiplicationOver φ
          ((g : Matrix (Fin 8) (Fin 8) A).mulVec x)
          ((g : Matrix (Fin 8) (Fin 8) A).mulVec y)

/-- An actual closed subgroup of `GL₈` realizes the algebra automorphism group
when its range is exactly the unit and multiplication equations on every test
scheme, including nonreduced tests. This is a predicate, not a representability
or existence assertion. -/
def IsAutomorphismRepresentation
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (iH : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)) : Prop :=
  IsClosedSubgroup iH ∧
    ∀ (T : Over (Spec (CommRingCat.of K)))
      (g : T ⟶ (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X),
      g ∈ (SubgroupFunctor.range iH).carrier T ↔
        c.IsAutomorphismMatrix
          (algebraMap (CommRingCat.of K) ((algΓ (CommRingCat.of K)).obj T).unop)
          (GeneralLinear.pointsEquiv (Fin 8) (CommRingCat.of K) T g)

end CayleyDatum

end Langlands.GroupScheme
