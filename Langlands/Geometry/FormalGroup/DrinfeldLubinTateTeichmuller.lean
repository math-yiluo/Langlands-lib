import Langlands.Geometry.FormalGroup.DrinfeldLubinTateLine
import Langlands.Algebra.LocalDivisionSubfieldHensel

/-! # Linear Teichmüller action on the reduced Lubin–Tate line -/

noncomputable section

namespace Langlands.FormalGroup

open MvPowerSeries

universe u v

namespace CoordinateMap

variable {A : Type u} [CommRing A]

/-- Ordinary multiplication of the sole formal variable by a coefficient. -/
def lineScale (a : A) : CoordinateMap A Unit Unit where
  series _ := a • X ()
  constantCoeff_eq_zero _ := by simp

@[simp]
theorem lineScale_map {B : Type v} [CommRing B] (φ : A →+* B) (a : A) :
    (lineScale a).map φ = lineScale (φ a) := by
  apply CoordinateMap.ext
  funext i
  change (a • X () : MvPowerSeries Unit A).map φ = φ a • X ()
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]

/-- Commutation with a linear scalar equates its `n`-th power and its first
power on each `n`-th coefficient. -/
theorem coeff_lineScale_commute {g : CoordinateMap A Unit Unit} (a : A)
    (h : g.comp (lineScale a) = (lineScale a).comp g) (n : ℕ) :
    a ^ n * PowerSeries.coeff n (g.series ()) = a * PowerSeries.coeff n (g.series ()) := by
  have hSeries := congrArg (fun g : CoordinateMap A Unit Unit => g.series ()) h
  change subst (fun _ : Unit => a • X ()) (g.series ()) = subst g.series (a • X ()) at hSeries
  have hv : ((fun _ : Unit => a) • (X : Unit → MvPowerSeries Unit A)) = (fun _ => a • X ()) := by
    funext i
    cases i
    rfl
  have hs := rescale_eq_subst (fun _ : Unit => a) (g.series ())
  rw [hv] at hs
  rw [← hs, subst_smul g.hasSubst, subst_X g.hasSubst] at hSeries
  have hc := congrArg (coeff (Finsupp.single () n)) hSeries
  rw [coeff_rescale, coeff_smul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply,
    Finsupp.degree_single] at hc
  exact hc

end CoordinateMap

namespace LubinTateStandard

open IsLocalRing CoordinateMap

variable {A : Type u} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [IsDomain A]
variable (π : A) (hπ : maximalIdeal A = Ideal.span {π}) (hπne : π ≠ 0)

include hπne in
/-- The scalar series for a Teichmüller lift with `a^q = a` is just `aX`. -/
theorem scalarMap_eq_lineScale_of_pow_eq (a : A) (h : a ^ Nat.card (ResidueField A) = a) :
    scalarMap π hπ a = lineScale a := by
  let q := Nat.card (ResidueField A)
  change a ^ q = a at h
  have hP := (polynomialCoordinates π Unit).hasSubst
  have he : Intertwines π (lineScale a) := by
    apply (intertwines_iff_defect π _).mpr
    intro i
    apply sub_eq_zero.mpr
    change π • (a • X ()) + (a • X () : MvPowerSeries Unit A) ^ q =
      subst (polynomialCoordinates π Unit).series (a • X ())
    rw [subst_smul hP, subst_X hP]
    change π • (a • X ()) + (a • X () : MvPowerSeries Unit A) ^ q = a • (π • X () + X () ^ q)
    simp [smul_pow, h, smul_add, smul_smul, mul_comm]
  apply ext_intertwines π hπ hπne (intertwines_scalarMap π hπ a) he
  intro i j
  cases i
  cases j
  rw [scalarMap_linearCoeff]
  change a = coeff (Finsupp.single () 1) (a • X () : MvPowerSeries Unit A)
  rw [coeff_smul, coeff_index_single_self_X, mul_one]

end LubinTateStandard

namespace LocalDivision

open ValuativeRel CentralDivision CentralSimple IsLocalRing

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance lubinTateTeichmullerLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "C" => SubfieldIntegerRing K D ι
local notation "k" => ResidueField (SubfieldIntegerRing K D ι)
local notation "q" => Nat.card (ResidueField (SubfieldIntegerRing K D ι))

variable [Finite (ResidueField (SubfieldIntegerRing K D ι))]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)

include hL in
/-- Each residue coefficient lifts to a root of the original `X^q − X`. -/
theorem subfield_exists_teichmuller (x : k) : ∃ a : C, residue C a = x ∧ a ^ q = a := by
  let : FiniteDimensional K L := hL.1
  let : Fintype k := Fintype.ofFinite k
  let P : Polynomial C := Polynomial.X ^ q - Polynomial.X
  have hq : 1 < q := Finite.one_lt_card
  have hMonic : P.Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hq
  have hRoot : P.eval₂ (residue C) x = 0 := by
    simp [P, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hDeriv : P.derivative.eval₂ (residue C) x ≠ 0 := by
    rw [show P.derivative = Polynomial.C (q : C) * Polynomial.X ^ (q - 1) - 1 by
      simp [P, Polynomial.derivative_X_pow]]
    simp
  have hH := (HenselianLocalRing.TFAE C).out 1 3
  obtain ⟨a, ha, hr⟩ := hH.mp (localDivisionSubfield_henselian K D ι)
    (residue C) residue_surjective P hMonic x hRoot hDeriv
  have hpow : a ^ q = a := by
    simpa [P, Polynomial.IsRoot.def, sub_eq_zero] using ha
  exact ⟨a, hr, hpow⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ) {π : 𝒪[K]} (hπ : Irreducible π)

local notation "Gbar" => drinfeldLubinTateGroup ι χ hL hπ
local notation "f" => drinfeldLubinTateCoefficients ι χ hL hπ
local notation "ϖ" => algebraMap 𝒪[K] C π
local notation "hgen" => subfieldMaximalIdeal_eq_uniformizer ι hL hπ
local notation "hne" => subfieldScalar_uniformizer_ne_zero ι hπ

/-- Every residue coefficient occurs as an exactly linear scalar action on the reduced line. -/
theorem drinfeldLubinTateCoefficients_has_lineScale (x : k) :
    ∃ a : C, (f a).toCoordinateMap = CoordinateMap.lineScale (χ x) := by
  obtain ⟨a, hr, ha⟩ := subfield_exists_teichmuller ι hL x
  refine ⟨a, ?_⟩
  let θ := subfieldReductionCharacter ι χ
  change (LubinTateStandard.scalarMap ϖ hgen a).map θ.toRingHom = _
  rw [LubinTateStandard.scalarMap_eq_lineScale_of_pow_eq ϖ hgen hne a ha, CoordinateMap.lineScale_map]
  change CoordinateMap.lineScale (χ (residue C a)) = _
  rw [hr]

/-- An endomorphism commuting with the coefficient action and with zero
linear term vanishes to at least the scalar uniformizer's degree. -/
theorem line_uniformizer_degree_dvd (g : CommLaw.Hom Gbar Gbar)
    (hg : ∀ a : C, Commute g (f a)) (hlin : g.toCoordinateMap.linearCoeff () () = 0) :
    (PowerSeries.X : PowerSeries κ) ^ q ∣ g.toCoordinateMap.series () := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro n hn
  by_cases hzero : n = 0
  · subst n
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact g.toCoordinateMap.constantCoeff_eq_zero ()
  by_cases hone : n = 1
  · subst n
    exact hlin
  by_contra hnz
  let : Fintype k := Fintype.ofFinite k
  have hAll (x : kˣ) : x ^ (n - 1) = 1 := by
    obtain ⟨a, ha⟩ := drinfeldLubinTateCoefficients_has_lineScale ι hL χ hπ (x : k)
    have hc := congrArg CommLaw.Hom.toCoordinateMap (hg a).eq
    change g.toCoordinateMap.comp (f a).toCoordinateMap = (f a).toCoordinateMap.comp g.toCoordinateMap at hc
    rw [ha] at hc
    have h := CoordinateMap.coeff_lineScale_commute (χ (x : k)) hc n
    have hpow : (χ (x : k)) ^ n = χ (x : k) := mul_right_cancel₀ hnz h
    have hx : χ (x : k) ≠ 0 := (map_ne_zero χ).mpr x.ne_zero
    have heq : (χ (x : k)) ^ (n - 1) * χ (x : k) = 1 * χ (x : k) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n), one_mul]
      exact hpow
    apply Units.ext
    exact χ.injective (calc
      χ ((x ^ (n - 1) : kˣ) : k) = χ (x : k) ^ (n - 1) := by
        rw [Units.val_pow_eq_pow_val, map_pow]
      _ = 1 := mul_right_cancel₀ hx heq
      _ = χ ((1 : kˣ) : k) := (map_one χ).symm)
  have hdvd := (FiniteField.forall_pow_eq_one_iff k (n - 1)).mp hAll
  have hd : q - 1 ≤ n - 1 := Nat.le_of_dvd (by omega)
    (by simpa only [Nat.card_eq_fintype_card] using hdvd)
  omega

end LocalDivision
end Langlands.FormalGroup
