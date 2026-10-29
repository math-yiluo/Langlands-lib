import Langlands.LocalField.RelativeIntegers
import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates

/-! Naturality of actual unit filtrations and their literal residue coordinates. -/

noncomputable section
namespace Langlands.PadicField.TopologicalData

universe u v
variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable (T : F.TopologicalData) (S : E.TopologicalData)

/-- The actual integer map preserves each power of the maximal ideal. -/
theorem relativeIntegerMap_mem_maximalIdeal_pow (n : ℕ) (a : T.Integers)
    (ha : a ∈ IsLocalRing.maximalIdeal T.Integers ^ n) :
    relativeIntegerMap T S a ∈ IsLocalRing.maximalIdeal S.Integers ^ n := by
  have hm := Ideal.mem_map_of_mem (relativeIntegerMap T S) ha
  rw [Ideal.map_pow] at hm
  exact (pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le (relativeIntegerMap T S)) n) hm

/-- The actual integer-unit map preserves congruence level, including zero. -/
theorem relativeIntegerMap_mem_congruenceUnits (n : ℕ) (x : T.Integersˣ)
    (hx : x ∈ T.congruenceUnits n) :
    Units.map (relativeIntegerMap T S).toMonoidHom x ∈ S.congruenceUnits n := by
  rw [S.mem_congruenceUnits_iff]
  change relativeIntegerMap T S (x : T.Integers) - 1 ∈ _
  rw [← map_one (relativeIntegerMap T S), ← map_sub]
  exact relativeIntegerMap_mem_maximalIdeal_pow T S n _
    ((T.mem_congruenceUnits_iff n x).mp hx)

/-- The given field embedding preserves every actual field-unit filtration level. -/
theorem relative_mem_unitFiltration (n : ℕ) (x : F.Carrierˣ)
    (hx : x ∈ T.unitFiltration n) :
    Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom x ∈ S.unitFiltration n := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨Units.map (relativeIntegerMap T S).toMonoidHom y,
    relativeIntegerMap_mem_congruenceUnits T S n y hy, ?_⟩
  apply Units.ext
  rfl

/-- Restriction of the given field-unit embedding to the existing filtration groups. -/
def relativeUnitFiltrationMap (n : ℕ) : T.unitFiltration n →* S.unitFiltration n where
  toFun x := ⟨Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom x,
    relative_mem_unitFiltration T S n x x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem relativeUnitFiltrationMap_apply (n : ℕ) (x : T.unitFiltration n) :
    (relativeUnitFiltrationMap T S n x : E.Carrierˣ) =
      Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom (x : F.Carrierˣ) := rfl

@[simp] theorem relativeUnitFiltrationMap_coe (n : ℕ) (x : T.unitFiltration n) :
    ((relativeUnitFiltrationMap T S n x : E.Carrierˣ) : E.Carrier) =
      algebraMap F.Carrier E.Carrier ((x : F.Carrierˣ) : F.Carrier) := rfl

/-- Recovering an integer unit commutes with the actual relative integer map. -/
theorem filtrationIntegerUnit_relativeUnitFiltrationMap (n : ℕ)
    (x : T.unitFiltration n) :
    S.filtrationIntegerUnit n (relativeUnitFiltrationMap T S n x) =
      Units.map (relativeIntegerMap T S).toMonoidHom (T.filtrationIntegerUnit n x) := by
  apply Units.ext
  apply Subtype.ext
  change ((S.filtrationIntegerUnit n (relativeUnitFiltrationMap T S n x) :
      S.Integers) : E.Carrier) =
    algebraMap F.Carrier E.Carrier ((T.filtrationIntegerUnit n x : T.Integers) : F.Carrier)
  rw [S.filtrationIntegerUnit_coe, T.filtrationIntegerUnit_coe]
  rfl

/-- Reduction of the recovered integer unit commutes with the actual residue map. -/
theorem zeroUnitCoordinate_relativeUnitFiltrationMap (x : T.unitFiltration 0) :
    S.zeroUnitCoordinate (relativeUnitFiltrationMap T S 0 x) =
      Units.map (relativeResidueMap T S).toMonoidHom (T.zeroUnitCoordinate x) := by
  apply Units.ext
  rw [S.zeroUnitCoordinate_val]
  rw [filtrationIntegerUnit_relativeUnitFiltrationMap]
  change S.residue (relativeIntegerMap T S (T.filtrationIntegerUnit 0 x : T.Integers)) =
    relativeResidueMap T S (T.residue (T.filtrationIntegerUnit 0 x : T.Integers))
  exact (relativeResidueMap_residue T S _).symm

variable (π : F.Carrier) (hπ : T.ord π = 1)
variable (hπS : S.ord (algebraMap F.Carrier E.Carrier π) = 1)

/-- Literal division coefficients commute with the actual field embedding whenever
the supplied source uniformizer is also a uniformizer after applying that embedding. -/
theorem unitCoefficient_relativeUnitFiltrationMap (n : ℕ) (x : T.unitFiltration n) :
    S.unitCoefficient (algebraMap F.Carrier E.Carrier π) hπS n
      (relativeUnitFiltrationMap T S n x) =
    relativeIntegerMap T S (T.unitCoefficient π hπ n x) := by
  apply Subtype.ext
  change
    ((((relativeUnitFiltrationMap T S n x : E.Carrierˣ) : E.Carrier) - 1) /
      (algebraMap F.Carrier E.Carrier π) ^ n) =
    algebraMap F.Carrier E.Carrier
      ((((x : F.Carrierˣ) : F.Carrier) - 1) / π ^ n)
  rw [map_div₀, map_sub, map_one, map_pow]
  rfl

/-- The residues of the literal coefficients commute with the actual residue map. -/
theorem residue_unitCoefficient_relativeUnitFiltrationMap (n : ℕ)
    (x : T.unitFiltration n) :
    S.residue (S.unitCoefficient (algebraMap F.Carrier E.Carrier π) hπS n
      (relativeUnitFiltrationMap T S n x)) =
    relativeResidueMap T S (T.residue (T.unitCoefficient π hπ n x)) := by
  rw [unitCoefficient_relativeUnitFiltrationMap T S π hπ hπS]
  exact (relativeResidueMap_residue T S _).symm

/-- Positive residue coordinates commute with the given residue-field embedding. -/
theorem positiveUnitCoordinate_relativeUnitFiltrationMap (n : ℕ) (hn : 0 < n)
    (x : T.unitFiltration n) :
    S.positiveUnitCoordinate (algebraMap F.Carrier E.Carrier π) hπS n hn
      (relativeUnitFiltrationMap T S n x) =
    Multiplicative.ofAdd
      (relativeResidueMap T S ((T.positiveUnitCoordinate π hπ n hn x).toAdd)) := by
  exact congrArg Multiplicative.ofAdd
    (residue_unitCoefficient_relativeUnitFiltrationMap T S π hπ hπS n x)

end Langlands.PadicField.TopologicalData
