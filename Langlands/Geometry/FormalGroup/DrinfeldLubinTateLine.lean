import Langlands.Geometry.FormalGroup.LubinTateStandardModule
import Langlands.Geometry.FormalGroup.DrinfeldSubfieldCharacters
import Langlands.Geometry.FormalGroup.PiDivisible

/-! # The Lubin–Tate line over a Drinfeld residue coefficient field -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple IsLocalRing ModuleLaw

universe u

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance ltLineLocalHom : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "C" => SubfieldIntegerRing K D ι

/-- The embedded unramified integer subfield has a finite residue field. -/
theorem subfieldResidueFinite (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    Finite (ResidueField C) := by
  let : Module.Finite 𝒪[K] C := hL.2.1
  exact ResidueField.finite_of_finite (R := 𝒪[K]) (S := C) inferInstance

/-- The original uniformizer generates the maximal ideal of the embedded unramified integers. -/
theorem subfieldMaximalIdeal_eq_uniformizer (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    {π : 𝒪[K]} (hπ : Irreducible π) : maximalIdeal C = Ideal.span {algebraMap 𝒪[K] C π} := by
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := 𝒪[K]) (S := C)
  rw [← h, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- The original uniformizer remains nonzero in the embedded field integers. -/
theorem subfieldScalar_uniformizer_ne_zero {π : 𝒪[K]} (hπ : Irreducible π) :
    algebraMap 𝒪[K] C π ≠ 0 := by
  intro h
  apply hπ.ne_zero
  apply Subtype.ext
  apply (algebraMap K L).injective
  have hc := congrArg (fun a : C => (a : L)) h
  change (algebraMap K L) (π : K) = 0 at hc
  exact hc.trans (map_zero (algebraMap K L)).symm

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)

/-- Evaluate embedded integer coefficients through the given residue embedding. -/
def subfieldReductionCharacter : C →ₐ[𝒪[K]] κ :=
  (χ.restrictScalars 𝒪[K]).comp (IsScalarTower.toAlgHom 𝒪[K] C (ResidueField C))

@[simp]
theorem subfieldReductionCharacter_apply (a : C) :
    subfieldReductionCharacter ι χ a = χ (residue C a) := rfl

variable [Finite (ResidueField (SubfieldIntegerRing K D ι))]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) {π : 𝒪[K]} (hπ : Irreducible π)

local notation "θ" => subfieldReductionCharacter ι χ
local notation "ϖ" => algebraMap 𝒪[K] C π
local notation "hgen" => subfieldMaximalIdeal_eq_uniformizer ι hL hπ
local notation "hne" => subfieldScalar_uniformizer_ne_zero ι hπ
local notation "G" => LubinTateStandard.commLaw ϖ hgen hne

/-- The reduced Lubin–Tate law over the residue coefficient field. -/
def drinfeldLubinTateGroup : CommLaw κ Unit := (G).map (θ).toRingHom

local notation "Gbar" => drinfeldLubinTateGroup ι χ hL hπ

/-- Reduction of the full embedded integer action to the residue coefficient field. -/
def drinfeldLubinTateCoefficients : C →+* CommLaw.Hom Gbar Gbar :=
  (CommLaw.Hom.mapEnd G (θ).toRingHom).comp (LubinTateStandard.scalarAction ϖ hgen hne)

local notation "f" => drinfeldLubinTateCoefficients ι χ hL hπ

/-- The reduced formal action retains the actual residue tangent character. -/
theorem drinfeldLubinTateCoefficients_linearCoeff (a : C) :
    (f a).toCoordinateMap.linearCoeff () () = χ (residue C a) := by
  change ((LubinTateStandard.scalarMap ϖ hgen a).map (θ).toRingHom).linearCoeff () () = _
  rw [CoordinateMap.linearCoeff_map, LubinTateStandard.scalarMap_linearCoeff]
  rfl

/-- Restrict the scalar action of the reduced line to the original local integers. -/
def drinfeldLubinTateLine : ModuleLaw 𝒪[K] κ Unit where
  groupLaw := Gbar
  action := (f).comp (algebraMap 𝒪[K] C)
  linear_natural a i j := by
    cases i
    cases j
    change (f (algebraMap 𝒪[K] C a)).toCoordinateMap.linearCoeff () () = _
    rw [drinfeldLubinTateCoefficients_linearCoeff]
    change θ (algebraMap 𝒪[K] C a) = _
    rw [AlgHom.commutes]
    simp [CoordinateMap.scalarLinearCoeff]

/-- The uniformizer in the embedded integers acts on the reduced line by the
residue-cardinality power of its coordinate. -/
theorem drinfeldLubinTateCoefficients_uniformizer_series :
    (f (ϖ)).toCoordinateMap.series () =
      (MvPowerSeries.X () : MvPowerSeries Unit κ) ^ Nat.card (ResidueField C) := by
  change ((LubinTateStandard.scalarMap ϖ hgen ϖ).map (θ).toRingHom).series () = _
  rw [LubinTateStandard.scalarMap_uniformizer ϖ hgen hne]
  change (LubinTateStandard.standardPolynomial ϖ (Nat.card (ResidueField C))
    (MvPowerSeries.X ())).map (θ).toRingHom = _
  have hzero : θ (ϖ) = 0 := by
    change χ (residue C (ϖ)) = 0
    rw [LubinTateStandard.residue_uniformizer ϖ hgen, map_zero]
  unfold LubinTateStandard.standardPolynomial
  rw [MvPowerSeries.smul_eq_C_mul, map_add, map_mul, MvPowerSeries.map_C,
    show (θ).toRingHom (ϖ) = 0 from hzero, map_zero, zero_mul, zero_add, map_pow, MvPowerSeries.map_X]

/-- The same power series describes the original scalar uniformizer on the reduced line. -/
theorem drinfeldLubinTateLine_uniformizer_series :
    ((drinfeldLubinTateLine ι χ hL hπ).scalarHom π).toHom.toCoordinateMap.series () =
      (MvPowerSeries.X () : MvPowerSeries Unit κ) ^ Nat.card (ResidueField C) := by
  simp only [scalarHom, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id]
  exact drinfeldLubinTateCoefficients_uniformizer_series ι χ hL hπ

end Langlands.FormalGroup.LocalDivision
