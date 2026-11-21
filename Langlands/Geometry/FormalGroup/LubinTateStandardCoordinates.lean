import Langlands.Geometry.FormalGroup.LubinTateStandardIntertwiner
import Langlands.Geometry.FormalGroup.Tangent
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.CoeffSingle

/-! # Pointed maps intertwining the standard Lubin–Tate polynomial -/

noncomputable section

namespace Langlands.FormalGroup.LubinTateStandard

open MvPowerSeries IsLocalRing CoordinateMap
open Langlands.NYLL.LubinTate.SameUniformizer
open scoped ENat

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)]
variable (π : A)

local notation "q" => Nat.card (ResidueField A)

/-- The standard polynomial in each coordinate, as an actual pointed map. -/
def polynomialCoordinates (σ : Type) : CoordinateMap A σ σ where
  series i := standardPolynomial π q (X i)
  constantCoeff_eq_zero i := standardPolynomial_constantCoeff π Nat.card_pos.ne' (constantCoeff_X i)

variable {σ τ υ : Type} [Fintype σ] [Fintype τ] [Fintype υ]

/-- A pointed map intertwines the standard polynomials on its source and target. -/
def Intertwines (f : CoordinateMap A σ τ) : Prop :=
  (polynomialCoordinates π τ).comp f = f.comp (polynomialCoordinates π σ)

omit [Fintype σ] in
private theorem polynomial_comp_series (f : CoordinateMap A σ τ) (i : τ) :
    ((polynomialCoordinates π τ).comp f).series i = standardPolynomial π q (f.series i) := by
  change subst f.series (π • X i + X i ^ q) = π • f.series i + f.series i ^ q
  rw [subst_add f.hasSubst, subst_smul f.hasSubst, subst_pow f.hasSubst, subst_X f.hasSubst]

/-- The coordinate equation is the same as vanishing of each individual defect. -/
theorem intertwines_iff_defect (f : CoordinateMap A σ τ) :
    Intertwines π f ↔ ∀ i, intertwinerDefect π q (f.series i) = 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun g : CoordinateMap A σ τ => g.series i) h
    rw [polynomial_comp_series] at hi
    exact sub_eq_zero.mpr hi
  · intro h
    apply CoordinateMap.ext
    funext i
    rw [polynomial_comp_series]
    exact sub_eq_zero.mp (h i)

namespace Intertwines

variable {π}

/-- Composing actual intertwiners gives an actual intertwiner. -/
theorem comp {f : CoordinateMap A σ τ} {g : CoordinateMap A τ υ}
    (hg : Intertwines π g) (hf : Intertwines π f) : Intertwines π (g.comp f) := by
  unfold Intertwines at *
  rw [← CoordinateMap.comp_assoc, hg, CoordinateMap.comp_assoc, hf, ← CoordinateMap.comp_assoc]

/-- Pairing actual intertwiners gives an actual intertwiner. -/
theorem pair {f : CoordinateMap A σ τ} {g : CoordinateMap A σ υ}
    (hf : Intertwines π f) (hg : Intertwines π g) : Intertwines π (f.pair g) := by
  rw [intertwines_iff_defect] at hf hg ⊢
  intro i
  cases i with
  | inl i => exact hf i
  | inr i => exact hg i

@[simp]
theorem id : Intertwines π (CoordinateMap.id (R := A) (σ := σ)) := by simp [Intertwines]

@[simp]
theorem zero : Intertwines π (CoordinateMap.zero (R := A) (σ := σ) (τ := τ)) := by simp [Intertwines]

/-- Selecting coordinate variables intertwines the componentwise polynomial. -/
theorem vars (v : τ → σ) : Intertwines π (CoordinateMap.vars (R := A) v) := by
  apply CoordinateMap.ext
  funext i
  rw [polynomial_comp_series, vars_series, comp_series, vars_series,
    subst_X (polynomialCoordinates π σ).hasSubst]
  rfl

@[simp]
theorem fst : Intertwines π (CoordinateMap.fst (R := A) (σ := σ) (τ := τ)) := vars Sum.inl

@[simp]
theorem snd : Intertwines π (CoordinateMap.snd (R := A) (σ := σ) (τ := τ)) := vars Sum.inr

@[simp]
theorem polynomial : Intertwines π (polynomialCoordinates π σ) := rfl

/-- An endomorphism of the coefficient ring that fixes the uniformizer preserves the equation. -/
theorem map {f : CoordinateMap A σ τ} (hf : Intertwines π f) (φ : A →+* A) (hφ : φ π = π) :
    Intertwines π (f.map φ) := by
  have he (S : Type) : (polynomialCoordinates π S).map φ = polynomialCoordinates π S := by
    apply CoordinateMap.ext
    funext i
    simp [polynomialCoordinates, standardPolynomial, smul_eq_C_mul, hφ]
  have h := congrArg (CoordinateMap.map φ) hf
  simpa only [Intertwines, CoordinateMap.map_comp, he] using h

end Intertwines

omit [IsLocalRing A] [Finite (ResidueField A)] [Fintype τ] in
private theorem hasLinearTerm_linearCoeff (f : CoordinateMap A σ τ) (i : τ) :
    HasLinearTerm (f.series i) (f.linearCoeff i) := by
  classical
  apply nat_le_order (n := 2)
  intro d hd
  rw [map_sub, sub_eq_zero]
  by_cases hzero : d = 0
  · subst d
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      f.constantCoeff_eq_zero, constantCoeff_linearForm]
  have hd0 : d.degree ≠ 0 := fun h => hzero ((Finsupp.degree_eq_zero_iff d).mp h)
  have hone : d.degree = 1 := by omega
  have hi : d ∈ Set.range (fun j : σ => Finsupp.single j 1) := by rwa [Finsupp.range_single_one]
  obtain ⟨j, rfl⟩ := hi
  simp [linearForm, coeff_C_mul, coeff_index_single_X, CoordinateMap.linearCoeff]

variable (hπ : maximalIdeal A = Ideal.span {π})

/-- Lift each row of a matrix to its integral standard intertwiner. -/
def liftLinear (L : Matrix τ σ A) : CoordinateMap A σ τ where
  series i := intertwiner π hπ (L i)
  constantCoeff_eq_zero i := (intertwiner_hasLinearTerm π hπ (L i)).constantCoeff_eq_zero

@[simp]
theorem intertwines_liftLinear (L : Matrix τ σ A) : Intertwines π (liftLinear π hπ L) :=
  (intertwines_iff_defect π _).mpr (fun i => intertwiner_defect_zero π hπ (L i))

omit [Fintype τ] in
@[simp]
theorem linearCoeff_liftLinear (L : Matrix τ σ A) (i : τ) (j : σ) :
    (liftLinear π hπ L).linearCoeff i j = L i j :=
  (intertwiner_hasLinearTerm π hπ (L i)).coeff_single j

variable [IsDomain A] (hπne : π ≠ 0)

include hπ hπne in
/-- Intertwiners are determined by their tangent coefficient matrices. -/
theorem ext_intertwines {f g : CoordinateMap A σ τ} (hf : Intertwines π f) (hg : Intertwines π g)
    (h : ∀ i j, f.linearCoeff i j = g.linearCoeff i j) : f = g := by
  apply CoordinateMap.ext
  funext i
  have hL : f.linearCoeff i = g.linearCoeff i := funext (h i)
  apply intertwiner_unique π hπ hπne (L := f.linearCoeff i) (hasLinearTerm_linearCoeff f i)
    (hL ▸ hasLinearTerm_linearCoeff g i)
  · exact (intertwines_iff_defect π _).mp hf i
  · exact (intertwines_iff_defect π _).mp hg i

include hπ hπne in
/-- Evaluation of the tangent map detects equality of intertwiners. -/
theorem ext_intertwines_tangent {f g : CoordinateMap A σ τ}
    (hf : Intertwines π f) (hg : Intertwines π g)
    (h : ∀ x i, f.linearPart x i = g.linearPart x i) : f = g := by
  classical
  apply ext_intertwines π hπ hπne hf hg
  intro i j
  have hi := h (Pi.single j 1) i
  simpa [linearPart_apply, Pi.single_apply, mul_ite] using hi

include hπne in
/-- Fixing the uniformizer and mapping coefficients sends the lifted linear map to the lift of the mapped matrix. -/
theorem map_liftLinear (φ : A →+* A) (hφ : φ π = π) (L : Matrix τ σ A) :
    (liftLinear π hπ L).map φ = liftLinear π hπ (fun i j => φ (L i j)) := by
  apply ext_intertwines π hπ hπne ((intertwines_liftLinear π hπ L).map φ hφ)
    (intertwines_liftLinear π hπ _)
  intro i j
  rw [CoordinateMap.linearCoeff_map, linearCoeff_liftLinear]
  exact (linearCoeff_liftLinear π hπ (fun i j => φ (L i j)) i j).symm

end Langlands.FormalGroup.LubinTateStandard
