import Langlands.Algebra.LocalUnitaryResidue
import Mathlib.Algebra.Algebra.Opposite

/-!
# Local division algebras isomorphic to their opposites
-/

noncomputable section

universe u

namespace Langlands

/-- The algebra has an algebra anti-equivalence fixing its scalar field. -/
def HasAlgebraAntiEquivalence (K D : Type u) [Field K] [DivisionRing D]
    [Algebra K D] : Prop :=
  Nonempty (D ≃ₐ[K] Dᵐᵒᵖ)

namespace AlgebraAntiEquivalence

open _root_.Polynomial

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (f : D ≃ₐ[K] Dᵐᵒᵖ)

/-- The product-reversing map underlying an equivalence with the opposite algebra. -/
def tau (x : D) : D := MulOpposite.unop (f x)

theorem tau_injective : Function.Injective (tau f) :=
  MulOpposite.unop_injective.comp f.injective

@[simp] theorem tau_zero : tau f 0 = 0 := by simp [tau]

@[simp] theorem tau_one : tau f 1 = 1 := by simp [tau]

theorem tau_add (x y : D) : tau f (x + y) = tau f x + tau f y := by
  simp [tau]

theorem tau_mul (x y : D) : tau f (x * y) = tau f y * tau f x := by
  simp [tau]

theorem tau_algebraMap (c : K) : tau f (algebraMap K D c) = algebraMap K D c := by
  simp [tau]

theorem tau_inv (x : D) : tau f x⁻¹ = (tau f x)⁻¹ := by
  simp [tau]

theorem tau_pow (x : D) (n : ℕ) : tau f (x ^ n) = tau f x ^ n := by
  simp [tau]

/-- The anti-equivalence on units, used only as a map of sets. -/
def tauUnit (j : Dˣ) : Dˣ :=
  Units.mk0 (tau f j) (fun h => j.ne_zero (tau_injective f (h.trans (tau_zero f).symm)))

@[simp] theorem tauUnit_coe (j : Dˣ) : ((tauUnit f j : Dˣ) : D) = tau f j := rfl

theorem tau_aeval (x : D) (p : K[X]) :
    tau f (aeval x p) = aeval (tau f x) p := by
  induction p using _root_.Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, tau_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, tau_mul, tau_pow, tau_algebraMap,
      Algebra.commutes]

variable [FiniteDimensional K D]

theorem minpoly_eq (x : D) : minpoly K (tau f x) = minpoly K x := by
  have hint : ∀ y : D, IsIntegral K y := fun y => Algebra.IsIntegral.isIntegral y
  have h1 : minpoly K (tau f x) ∣ minpoly K x := by
    apply minpoly.dvd
    rw [← tau_aeval, minpoly.aeval, tau_zero]
  have h2 : minpoly K x ∣ minpoly K (tau f x) := by
    apply minpoly.dvd
    apply tau_injective f
    rw [tau_aeval, minpoly.aeval, tau_zero]
  have hd := natDegree_le_of_dvd h2 (minpoly.monic (hint (tau f x))).ne_zero
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hint (tau f x)))
    (minpoly.monic (hint x)) h1 hd).symm

theorem adjoinRank_eq (x : D) :
    UnitaryInvolution.adjoinRank K (tau f x) = UnitaryInvolution.adjoinRank K x := by
  have h1 := UnitaryInvolution.finrank_eq_natDegree_mul_adjoinRank K (tau f x)
  have h2 := UnitaryInvolution.finrank_eq_natDegree_mul_adjoinRank K x
  rw [minpoly_eq] at h1
  have hpos : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

/-- An algebra anti-equivalence preserves the regular norm, without an involutivity premise. -/
theorem norm_eq (x : D) : Algebra.norm K (tau f x) = Algebra.norm K x := by
  rw [UnitaryInvolution.norm_eq_minpoly_coeff, UnitaryInvolution.norm_eq_minpoly_coeff,
    adjoinRank_eq, minpoly_eq]

section Local

open Langlands.CentralDivision Langlands.DivisionValuation ValuativeRel

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D]

local instance : Field (Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D

/-- An algebra anti-equivalence preserves the canonical valuation. -/
theorem valuation_tau (x : D) :
    localReducedNormValuation K D (tau f x) = localReducedNormValuation K D x := by
  have h1 := valuation_regularNorm_eq_localReducedNormValuation_pow K D (tau f x)
  have h2 := valuation_regularNorm_eq_localReducedNormValuation_pow K D x
  rw [norm_eq, h2] at h1
  exact ((pow_left_inj₀ zero_le zero_le (CentralSimple.reducedDegree_pos K D).ne').mp h1).symm

/-- The anti-equivalence on the valuation integer subring. -/
def tauInteger (x : (localReducedNormValuation K D).integer) :
    (localReducedNormValuation K D).integer :=
  ⟨tau f x, by
    change localReducedNormValuation K D (tau f x) ≤ 1
    rw [valuation_tau]
    exact x.prop⟩

@[simp] theorem tauInteger_coe (x : (localReducedNormValuation K D).integer) :
    (tauInteger f x : D) = tau f x := rfl

/-- Reduction after the anti-equivalence is a ring map into the commutative residue field. -/
def tauReductionHom :
    (localReducedNormValuation K D).integer →+* Residue (localReducedNormValuation K D) where
  toFun x := reduction _ (tauInteger f x)
  map_one' := by
    rw [← map_one (reduction (localReducedNormValuation K D))]
    congr 1
    exact Subtype.ext (tau_one f)
  map_mul' x y := by
    have h : tauInteger f (x * y) = tauInteger f y * tauInteger f x :=
      Subtype.ext (tau_mul f x y)
    rw [h, map_mul, mul_comm]
  map_zero' := by
    rw [← map_zero (reduction (localReducedNormValuation K D))]
    congr 1
    exact Subtype.ext (tau_zero f)
  map_add' x y := by
    have h : tauInteger f (x + y) = tauInteger f x + tauInteger f y :=
      Subtype.ext (tau_add f x y)
    rw [h, map_add]

/-- The endomorphism induced by the anti-equivalence on the residue field. -/
def tauResidue :
    Residue (localReducedNormValuation K D) →+* Residue (localReducedNormValuation K D) :=
  Ideal.Quotient.lift (strictIdeal _) (tauReductionHom f) (fun x hx => by
    apply (reduction_eq_zero_iff _ _).mpr
    change localReducedNormValuation K D (tau f x) < 1
    rw [valuation_tau]
    exact hx)

@[simp] theorem tauResidue_reduction (x : (localReducedNormValuation K D).integer) :
    tauResidue f (reduction _ x) = reduction _ (tauInteger f x) := rfl

theorem tauResidue_conj (j : Dˣ) (r : Residue (localReducedNormValuation K D)) :
    conjResidue _ (tauUnit f j) (tauResidue f (conjResidue _ j r)) =
      tauResidue f r := by
  obtain ⟨x, rfl⟩ := reduction_surjective _ r
  rw [conjResidue_reduction, tauResidue_reduction, conjResidue_reduction,
    tauResidue_reduction]
  congr 1
  apply Subtype.ext
  simp only [conjInteger_coe, tauInteger_coe, Units.val_inv_eq_inv_val]
  rw [tau_mul, tau_mul, tau_inv]
  have hj : tau f (j : D) ≠ 0 := (tauUnit f j).ne_zero
  change tau f j * ((tau f j)⁻¹ * (tau f x * tau f j)) * (tau f j)⁻¹ = tau f x
  rw [mul_inv_cancel_left₀ hj, mul_inv_cancel_right₀ hj]

include f

/-- Under an anti-equivalence, every unit's residue conjugation has order dividing two. -/
theorem conjResidue_conjResidue (j : Dˣ) (s : Residue (localReducedNormValuation K D)) :
    conjResidue _ j (conjResidue _ j s) = s := by
  let v := localReducedNormValuation K D
  let ψ := conjResidue v j
  let t := tauResidue f
  have hcomm : ∀ a b : Residue v, a * b = b * a := localDivisionResidue_mul_comm K D
  have : Finite (Residue v) := localDivisionResidue_finite K D
  have h2 : ∀ s, conjResidue v (tauUnit f j) s = ψ s := fun s =>
    conjResidue_eq_of_value_eq v hcomm j (tauUnit f j) (valuation_tau f j).symm s
  have h1 : ∀ s, ψ (t (ψ s)) = t s := fun s => by
    rw [← h2]
    exact tauResidue_conj f j s
  apply t.injective
  calc
    t (ψ (ψ s)) = ψ (t (ψ s)) := UnitaryInvolution.finiteField_ringHom_comm t ψ (ψ s)
    _ = t s := h1 s

/-- A central division algebra over a nonarchimedean local field that is isomorphic to
its opposite has reduced degree dividing two. No involutivity is required. -/
theorem reducedDegree_dvd_two : CentralSimple.reducedDegree K D ∣ 2 := by
  obtain ⟨j, hj⟩ := exists_unit_conjResidue_faithful K D
  apply hj 2
  intro r
  rw [conjResidue_pow]
  exact conjResidue_conjResidue f j r

end Local

end AlgebraAntiEquivalence

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D]

theorem HasAlgebraAntiEquivalence.reducedDegree_dvd_two (h : HasAlgebraAntiEquivalence K D) :
    CentralSimple.reducedDegree K D ∣ 2 := by
  obtain ⟨f⟩ := h
  exact AlgebraAntiEquivalence.reducedDegree_dvd_two f

theorem not_hasAlgebraAntiEquivalence_of_two_lt (h : 2 < CentralSimple.reducedDegree K D) :
    ¬ HasAlgebraAntiEquivalence K D := by
  intro hf
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hf.reducedDegree_dvd_two
  omega

end Langlands
