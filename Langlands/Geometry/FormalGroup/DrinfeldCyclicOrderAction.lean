import Langlands.Geometry.FormalGroup.DrinfeldIntegralCyclicCoordinates
import Langlands.Geometry.FormalGroup.DrinfeldIntegralCyclicRelations

/-! # Extending a coefficient action to the division order -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision Langlands.ClassFieldTheory.Local
open Langlands.LocalField Langlands.LocalGalois Langlands.LocalGalois.Separable

universe u v

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
  (hE : ArithmeticUnramified K E) (ι : E →ₐ[K] D)
  (hdegree : Module.finrank K E = CentralSimple.reducedDegree K D)
variable {π : 𝒪[K]} (hπ : Irreducible π) {j : Dˣ} {σ : E ≃ₐ[K] E}
  (hpower : (j : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (horder : orderOf σ = CentralSimple.reducedDegree K D)
  (hconj : ∀ a : E, (j : D) * ι a = ι (σ a) * (j : D))

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι
local notation "O_D" => IntegerRing K D
local notation "iC" => subfieldIntegerInclusion K D ι
local notation "J" => drinfeldIntegralUniformizer j hpower
local notation "coords" => integerCyclicCoordinates K D E hE ι hdegree hπ hpower horder hconj
local notation "τ" => subfieldIntegerFrobenius ι σ
  (subfieldArithmeticUnramifiedOfReducedDegree K D E ι hE hdegree)
local notation "p" => (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι) π)

/-- The inverse of the integral coordinate equivalence is the cyclic sum in the order. -/
theorem integerCyclicCoordinates_symm_apply (a : Fin d → C) :
    (coords).symm a = ∑ i, iC (a i) * J ^ i.val := by
  let := localDivisionSubfieldLeftModule K D ι
  let b := implementingUnitBasis K D ι hconj hdegree horder
  let incl := (localReducedNormValuation K D).integer.subtype
  apply Subtype.ext
  change b.equivFun.symm (fun i => (a i : E)) = incl (∑ i, iC (a i) * J ^ i.val)
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow]
  change ι (a i : E) * b i = ι (a i : E) * (j : D) ^ i.val
  rw [implementingUnitBasis_apply]

/-- Integral cyclic coordinates preserve addition. -/
def integerCyclicAddCoordinates : O_D ≃+ (Fin d → C) :=
  { coords with
    map_add' := fun x y => by
      change coords (x + y) = coords x + coords y
      have h (a b : Fin d → C) : (coords).symm (a + b) = (coords).symm a + (coords).symm b := by
        simp only [integerCyclicCoordinates_symm_apply, Pi.add_apply, map_add, add_mul,
          Finset.sum_add_distrib]
      apply (coords).symm.injective
      simpa only [(coords).symm_apply_apply] using (h (coords x) (coords y)).symm }

include hE hdegree hπ horder hconj in
private theorem cyclicCoordinates_monomial (a : C) (i : Fin d) :
    coords (iC a * J ^ i.val) = fun k => if k = i then a else 0 := by
  let c : Fin d → C := fun k => if k = i then a else 0
  have h := (coords).apply_symm_apply c
  rw [integerCyclicCoordinates_symm_apply] at h
  have hsum : (∑ k, iC (c k) * J ^ k.val) = iC a * J ^ i.val := by
    rw [Finset.sum_eq_single i]
    · simp [c]
    · intro k _ hki
      simp [c, hki]
    · simp
  rwa [hsum] at h

private theorem cyclic_monomial_mul {B A S : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Semiring S] (s : A ≃ₐ[B] A) (f : A →+* S) (t : S)
    (ht : ∀ a : A, t * f a = f (s a) * t) (a b : A) (n m : ℕ) :
    (f a * t ^ n) * (f b * t ^ m) = f (a * (s ^ n) b) * t ^ (n + m) := by
  have hpow (k : ℕ) : t ^ k * f b = f ((s ^ k) b) * t ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : (s ^ (k + 1)) b = s ((s ^ k) b) := by rw [pow_succ', AlgEquiv.mul_apply]
      rw [hs, pow_succ', mul_assoc, ih, ← mul_assoc, ht, mul_assoc]
  calc
    _ = f a * ((t ^ n * f b) * t ^ m) := by simp only [mul_assoc]
    _ = f a * (f ((s ^ n) b) * (t ^ n * t ^ m)) := by rw [hpow, mul_assoc]
    _ = _ := by rw [map_mul, pow_add, mul_assoc]

variable {S : Type v} [Semiring S] (f : SubfieldIntegerRing K D ι →+* S) (t : S)

private def cyclicOrderAddHom : O_D →+ S :=
  let sum : (Fin d → C) →+ S :=
    { toFun := fun a => ∑ i : Fin d, f (a i) * t ^ i.val
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] }
  sum.comp (integerCyclicAddCoordinates E hE ι hdegree hπ hpower horder hconj).toAddMonoidHom

variable (htpow : t ^ CentralSimple.reducedDegree K D = f (algebraMap 𝒪[K] _ π))
  (htconj : ∀ a : SubfieldIntegerRing K D ι, t * f a =
    f (subfieldIntegerFrobenius ι σ
      (subfieldArithmeticUnramifiedOfReducedDegree K D E ι hE hdegree) a) * t)

include htpow in
private theorem cyclicOrderAddHom_monomial (n : ℕ) (a : C) :
    cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t (iC a * J ^ n) =
      f a * t ^ n := by
  let A := cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t
  have hj : J ^ d = iC p := by
    rw [drinfeldIntegralUniformizer_pow, AlgHom.commutes]
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < d
    · let i : Fin d := ⟨n, hn⟩
      change (∑ k, f (coords (iC a * J ^ i.val) k) * t ^ k.val) = f a * t ^ i.val
      simp only [cyclicCoordinates_monomial]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [hki]
      · simp
    · let m := n - d
      have hnm : n = d + m := by dsimp [m]; omega
      have hmn : m < n := by
        have hd := CentralSimple.reducedDegree_pos K D
        omega
      change A (iC a * J ^ n) = f a * t ^ n
      calc
        _ = A (iC (a * p) * J ^ m) := by rw [hnm, pow_add, hj, map_mul (iC), mul_assoc]
        _ = f (a * p) * t ^ m := ih m hmn (a * p)
        _ = _ := by rw [hnm, pow_add, map_mul, ← htpow, mul_assoc]

include htpow htconj in
/-- A coefficient representation and an endomorphism satisfying the cyclic
relations extend to a representation of the actual division order. -/
def liftCyclicOrder : O_D →+* S where
  __ := cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t
  map_one' := by
    change cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t 1 = 1
    simpa only [map_one, pow_zero, mul_one] using
      cyclicOrderAddHom_monomial E hE ι hdegree hπ hpower horder hconj f t htpow 0 1
  map_mul' x y := by
    let A := cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t
    let a := coords x
    let b := coords y
    have hx : x = ∑ i, iC (a i) * J ^ i.val :=
      ((coords).symm_apply_apply x).symm.trans (integerCyclicCoordinates_symm_apply E hE ι hdegree hπ
        hpower horder hconj a)
    have hy : y = ∑ k, iC (b k) * J ^ k.val :=
      ((coords).symm_apply_apply y).symm.trans (integerCyclicCoordinates_symm_apply E hE ι hdegree hπ
        hpower horder hconj b)
    have hj (c : C) : J * iC c = iC (τ c) * J :=
      drinfeldIntegralUniformizer_mul_subfield ι j σ hpower hconj
        (subfieldArithmeticUnramifiedOfReducedDegree K D E ι hE hdegree) c
    change A (x * y) = A x * A y
    rw [hx, hy]
    simp only [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    have hA (c : C) (n : ℕ) : A (iC c * J ^ n) = f c * t ^ n :=
      cyclicOrderAddHom_monomial E hE ι hdegree hπ hpower horder hconj f t htpow n c
    calc
      _ = A (iC (a i * (τ ^ i.val) (b k)) * J ^ (i.val + k.val)) :=
        congrArg A (cyclic_monomial_mul τ (iC).toRingHom J hj (a i) (b k) i.val k.val)
      _ = f (a i * (τ ^ i.val) (b k)) * t ^ (i.val + k.val) := hA _ _
      _ = _ := by
        rw [hA, hA]
        exact (cyclic_monomial_mul τ f t htconj (a i) (b k) i.val k.val).symm

@[simp]
theorem liftCyclicOrder_subfield (a : C) :
    liftCyclicOrder E hE ι hdegree hπ hpower horder hconj f t htpow htconj (iC a) = f a := by
  change cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t (iC a) = f a
  simpa only [pow_zero, mul_one] using
    cyclicOrderAddHom_monomial E hE ι hdegree hπ hpower horder hconj f t htpow 0 a

@[simp]
theorem liftCyclicOrder_uniformizer :
    liftCyclicOrder E hE ι hdegree hπ hpower horder hconj f t htpow htconj J = t := by
  change cyclicOrderAddHom E hE ι hdegree hπ hpower horder hconj f t J = t
  simpa only [map_one, pow_one, one_mul] using
    cyclicOrderAddHom_monomial E hE ι hdegree hπ hpower horder hconj f t htpow 1 1

include hE hdegree hπ horder hconj in
/-- A map out of the order is determined by its values on the coefficients and uniformizer. -/
theorem cyclicOrderHom_ext {F G : O_D →+* S}
    (hf : ∀ a : C, F (iC a) = G (iC a)) (hj : F J = G J) : F = G := by
  ext x
  have hx := integerCyclicCoordinates_symm_apply E hE ι hdegree hπ hpower horder hconj (coords x)
  rw [(coords).symm_apply_apply] at hx
  rw [hx]
  simp only [map_sum, map_mul, map_pow, hf, hj]

end Langlands.FormalGroup.LocalDivision
