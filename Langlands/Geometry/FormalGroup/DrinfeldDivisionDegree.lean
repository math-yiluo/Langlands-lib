import Langlands.Geometry.FormalGroup.DrinfeldActionExponent
import Langlands.Geometry.FormalGroup.DivisionOrderRationalTwist
import Langlands.Geometry.FormalGroup.FieldDegreeUnits
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U014.Proofs

/-! # The degree of the rational division action on a formal module -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.FormalGroup.LocalDivision.DrinfeldAction

open ValuativeRel CentralSimple ModuleLaw

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {π : 𝒪[K]}

/-- A field unit given by an irreducible integer-ring element has normalized order one. -/
theorem fieldOrderUnits_uniformizer (hπ : Irreducible π) (t : Kˣ)
    (ht : (t : K) = algebraMap 𝒪[K] K π) : (Plancherel.fieldOrderUnits K t).toAdd = 1 := by
  have h := Langlands.NYLL.LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible
    K π hπ
  change FML.normalizedMultiplicativeValuation K (algebraMap 𝒪[K] K π) =
    WithZero.exp (-1 : ℤ) at h
  rw [Plancherel.fieldOrderUnits_toAdd, ht, h, WithZero.log_exp, neg_neg]

variable {D k : Type u} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] [Field k] [Algebra 𝒪[K] k]
variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] k σ}

/-- Apply the kernel-rank character to the actual fraction-field extension of the order action. -/
def divisionDegree (E : OrderAction (IntegerRing K D) M) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) : Dˣ →* ℚˣ :=
  (QuasiIsogeny.fieldDegreeUnits hπ hM).comp (Units.map (rationalAction K D E).toMonoidHom)

@[simp]
theorem divisionDegree_integerUnit (E : OrderAction (IntegerRing K D) M) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (a : (IntegerRing K D)ˣ) :
    divisionDegree E hπ hM (integerUnit K D a) = 1 := by
  apply Units.ext
  let e := (twistUnitIso K D E a⁻¹).toModuleIso
  have he : QuasiIsogeny.ofEndUnit
      (Units.map (rationalAction K D E).toMonoidHom (integerUnit K D a)) =
      QuasiIsogeny.ofIso (F := K) e := by
    apply QuasiIsogeny.ext
    change rationalAction K D E ((a : IntegerRing K D) : D) =
      RationalHom.ofHom (E.action (((a⁻¹)⁻¹ : (IntegerRing K D)ˣ) : IntegerRing K D))
    rw [inv_inv, rationalAction_coe]
  change (QuasiIsogeny.ofEndUnit
      (Units.map (rationalAction K D E).toMonoidHom (integerUnit K D a))).fieldDegree hπ hM hM = 1
  rw [he, QuasiIsogeny.fieldDegree_ofIso]

/-- The division character evaluates central scalars through the original formal scalar action. -/
theorem divisionDegree_uniformizer {q H : ℕ} (E : OrderAction (IntegerRing K D) M)
    (hπ : Irreducible π) (hM : M.HasPiHeight π q H) (t : Kˣ)
    (ht : (t : K) = algebraMap 𝒪[K] K π) :
    (divisionDegree E hπ hM.piDivisible (Units.map (algebraMap K D).toMonoidHom t) : ℚ) = (q : ℚ) ^ H := by
  have he :
      Units.map (rationalAction K D E).toMonoidHom (Units.map (algebraMap K D).toMonoidHom t) =
        Units.map (algebraMap K (RationalHom K M M)).toMonoidHom t := by
    apply Units.ext
    exact (rationalAction K D E).commutes (t : K)
  change (QuasiIsogeny.fieldDegreeUnits hπ hM.piDivisible
    (Units.map (rationalAction K D E).toMonoidHom (Units.map (algebraMap K D).toMonoidHom t)) : ℚ) = _
  rw [he]
  exact QuasiIsogeny.fieldDegreeUnits_uniformizer hπ hM t ht

/-- A scalar height `H*d` gives the division-unit degree `q^(H*ord(Nrd g))`. -/
theorem divisionDegree_eq_zpow {q H : ℕ} (hq : 0 < q) (E : OrderAction (IntegerRing K D) M)
    (hπ : Irreducible π) (hM : M.HasPiHeight π q (H * reducedDegree K D)) (g : Dˣ) :
    (divisionDegree E hπ hM.piDivisible g : ℚ) =
      (q : ℚ) ^ ((H : ℤ) * (divisionUnitOrder K D g).toAdd) := by
  let μ := divisionDegree E hπ hM.piDivisible
  let d := reducedDegree K D
  let r := (divisionUnitOrder K D g).toAdd
  let t := Units.mk0 (algebraMap 𝒪[K] K π)
    (fun h => hπ.ne_zero ((IsFractionRing.injective 𝒪[K] K) (h.trans (map_zero _).symm)))
  let s := Units.map (algebraMap K D).toMonoidHom t
  obtain ⟨a, ha⟩ := exists_divisionUnitOrder_correction K D g t (fieldOrderUnits_uniformizer hπ t rfl)
  have hp := congrArg μ ha
  change μ (integerUnit K D a) = μ (s ^ (-r) * g ^ d) at hp
  rw [divisionDegree_integerUnit, map_mul, map_zpow, map_pow] at hp
  have hpow : (μ g) ^ d = (μ s) ^ r := calc
    _ = ((μ s) ^ (-r))⁻¹ * ((μ s) ^ (-r) * (μ g) ^ d) := by simp
    _ = _ := by rw [← hp, mul_one, zpow_neg, inv_inv]
  have hs : (μ s : ℚ) = (q : ℚ) ^ (H * d) := divisionDegree_uniformizer E hπ hM t rfl
  have hval := congrArg (fun x : ℚˣ => (x : ℚ)) hpow
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, hs] at hval
  change (μ g : ℚ) = (q : ℚ) ^ ((H : ℤ) * r)
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  apply (pow_left_inj₀ (QuasiIsogeny.fieldDegreeUnits_pos hπ hM.piDivisible _).le
    (zpow_pos hq' _).le (reducedDegree_pos K D).ne').mp
  refine hval.trans ?_
  rw [← zpow_natCast (q : ℚ) (H * d), ← zpow_natCast ((q : ℚ) ^ ((H : ℤ) * r)) d,
    ← zpow_mul, ← zpow_mul, Nat.cast_mul]
  congr 1
  ring

/-- The forward map to the conjugated order acts by the inverse and has the opposite exponent. -/
theorem twistQuasiIsogeny_fieldDegree {q H : ℕ} (hq : 0 < q) (E : OrderAction (IntegerRing K D) M)
    (hπ : Irreducible π) (hM : M.HasPiHeight π q (H * reducedDegree K D)) (g : Dˣ) :
    (twistQuasiIsogeny K D E g).toModuleQuasiIsogeny.fieldDegree hπ hM.piDivisible hM.piDivisible =
      (q : ℚ) ^ (-(H : ℤ) * (divisionUnitOrder K D g).toAdd) := by
  have h := divisionDegree_eq_zpow hq E hπ hM g⁻¹
  have ho : (divisionUnitOrder K D g⁻¹).toAdd = -(divisionUnitOrder K D g).toAdd :=
    congrArg Multiplicative.toAdd ((divisionUnitOrder K D).map_inv g)
  have he : (twistQuasiIsogeny K D E g).toModuleQuasiIsogeny =
      QuasiIsogeny.ofEndUnit (Units.map (rationalAction K D E).toMonoidHom g⁻¹) :=
    QuasiIsogeny.ext rfl
  rw [ho] at h
  rw [he, ← QuasiIsogeny.fieldDegreeUnits_val]
  simpa only [divisionDegree, MonoidHom.comp_apply, mul_neg, neg_mul] using h

end Langlands.FormalGroup.LocalDivision.DrinfeldAction
