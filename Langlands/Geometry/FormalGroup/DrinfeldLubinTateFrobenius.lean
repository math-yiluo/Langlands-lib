import Langlands.Geometry.FormalGroup.DrinfeldLubinTateLine
import Langlands.Geometry.FormalGroup.RelativeFrobenius

/-! # The arithmetic Frobenius operator of the reduced Lubin–Tate line -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple IsLocalRing ModuleLaw

universe u

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance ltFrobeniusLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "C" => SubfieldIntegerRing K D ι
local notation "d" => CentralSimple.reducedDegree K D

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable [Finite (ResidueField (SubfieldIntegerRing K D ι))]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) {π : 𝒪[K]} (hπ : Irreducible π)
variable (p : ℕ) [ExpChar κ p] {e : ℕ} (hcard : Nat.card 𝓀[K] = p ^ e)

local notation "ϖ" => algebraMap 𝒪[K] C π
local notation "hgen" => subfieldMaximalIdeal_eq_uniformizer ι hL hπ
local notation "hne" => subfieldScalar_uniformizer_ne_zero ι hπ
local notation "G" => LubinTateStandard.commLaw ϖ hgen hne
local notation "Gbar" => drinfeldLubinTateGroup ι χ hL hπ
local notation "θ" => subfieldReductionCharacter ι χ
local notation "F" => iterateFrobenius κ p e
local notation "H" => drinfeldLubinTateLine ι χ hL hπ
local notation "f" => drinfeldLubinTateCoefficients ι χ hL hπ

include hL in
private theorem subfieldResidue_card : Nat.card (ResidueField C) = Nat.card 𝓀[K] ^ d := by
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[K]), subfieldResidue_finrank ι hL]

include hcard in
/-- The original scalar uniformizer is the reduced-degree iterate of arithmetic Frobenius. -/
theorem drinfeldLubinTateLine_uniformizer_frobenius :
    ((H).scalarHom π).toHom.toCoordinateMap = CoordinateMap.frobeniusPow p (e * d) := by
  apply CoordinateMap.ext
  funext i
  cases i
  rw [drinfeldLubinTateLine_uniformizer_series ι χ hL hπ, CoordinateMap.frobeniusPow_series,
    subfieldResidue_card ι hL, hcard, pow_mul]

variable (σ : L ≃ₐ[K] L)
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "τ" => subfieldIntegerFrobenius ι σ hL

include hσ hcard in
omit [Finite (ResidueField (SubfieldIntegerRing K D ι))] in
private theorem subfieldReductionCharacter_frobenius :
    (F).comp (θ).toRingHom = (θ).toRingHom.comp (τ).toAlgHom.toRingHom := by
  ext a
  change χ (residue C a) ^ (p ^ e) = χ (residue C (τ a))
  rw [← hcard, subfieldIntegerFrobenius_residue_pow ι σ hL hσ, map_pow]

include hσ hcard in
private theorem drinfeldLubinTateAddition_frobenius : (Gbar).addition.map (F) = (Gbar).addition := by
  have hτ : (τ).toAlgHom.toRingHom (ϖ) = ϖ := (τ).commutes π
  have he := congrArg (fun g : CommLaw C Unit => g.addition)
    (LubinTateStandard.commLaw_map ϖ hgen hne (τ).toAlgHom.toRingHom hτ)
  change ((G).addition.map (θ).toRingHom).map (F) = (G).addition.map (θ).toRingHom
  rw [CoordinateMap.map_ringHom_comp, subfieldReductionCharacter_frobenius ι χ hL p hcard σ hσ,
    ← CoordinateMap.map_ringHom_comp]
  exact congrArg (CoordinateMap.map (θ).toRingHom) he

include hσ hcard in
/-- Arithmetic Frobenius acts by a formal endomorphism of the reduced Lubin–Tate line. -/
def drinfeldLubinTateFrobenius : CommLaw.Hom Gbar Gbar where
  toCoordinateMap := CoordinateMap.frobeniusPow p e
  map_add := by
    rw [CoordinateMap.frobeniusPow_pair]
    have h := CoordinateMap.frobeniusPow_natural p e (Gbar).addition
    rw [drinfeldLubinTateAddition_frobenius ι χ hL hπ p hcard σ hσ] at h
    exact h

local notation "T" => drinfeldLubinTateFrobenius ι χ hL hπ p hcard σ hσ

/-- Frobenius on the line conjugates the coefficients by the original arithmetic automorphism. -/
theorem drinfeldLubinTateFrobenius_mul (a : C) : T * f a = f (τ a) * T := by
  have hτ : (τ).toAlgHom.toRingHom (ϖ) = ϖ := (τ).commutes π
  have hmap : (f a).toCoordinateMap.map (F) = (f (τ a)).toCoordinateMap := by
    change ((LubinTateStandard.scalarMap ϖ hgen a).map (θ).toRingHom).map (F) =
      (LubinTateStandard.scalarMap ϖ hgen (τ a)).map (θ).toRingHom
    rw [CoordinateMap.map_ringHom_comp, subfieldReductionCharacter_frobenius ι χ hL p hcard σ hσ,
      ← CoordinateMap.map_ringHom_comp, LubinTateStandard.scalarMap_map ϖ hgen hne _ hτ]
    rfl
  apply CommLaw.Hom.ext
  change (CoordinateMap.frobeniusPow p e).comp (f a).toCoordinateMap =
    (f (τ a)).toCoordinateMap.comp (CoordinateMap.frobeniusPow p e)
  rw [CoordinateMap.frobeniusPow_natural, hmap]

/-- Iterating the endomorphism raises the original coordinate by the corresponding Frobenius power. -/
theorem drinfeldLubinTateFrobenius_pow_coordinates (n : ℕ) :
    (T ^ n).toCoordinateMap = CoordinateMap.frobeniusPow p (e * n) := by
  induction n with
  | zero =>
    simp only [pow_zero, mul_zero, CoordinateMap.frobeniusPow_zero]
    rfl
  | succ n ih =>
    rw [pow_succ]
    change ((T ^ n).toCoordinateMap).comp (CoordinateMap.frobeniusPow p e) = _
    rw [ih, ← CoordinateMap.frobeniusPow_add, Nat.mul_succ, Nat.add_comm e]

/-- The reduced-degree power of the line Frobenius is the central scalar uniformizer. -/
theorem drinfeldLubinTateFrobenius_pow : T ^ d = f (ϖ) := by
  apply CommLaw.Hom.ext
  rw [drinfeldLubinTateFrobenius_pow_coordinates]
  apply CoordinateMap.ext
  funext i
  cases i
  rw [CoordinateMap.frobeniusPow_series, drinfeldLubinTateCoefficients_uniformizer_series ι χ hL hπ,
    subfieldResidue_card ι hL, hcard, pow_mul]

end Langlands.FormalGroup.LocalDivision
