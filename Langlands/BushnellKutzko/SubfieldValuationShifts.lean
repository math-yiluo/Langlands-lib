import Langlands.BushnellKutzko.SubfieldLatticeChain

/-! # The normalized subfield valuation and shifts of the chain -/

noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace Langlands.BushnellKutzko

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  (E : Type uE) [Field E] [Algebra F E]

local notation "𝒪ₑ[" F "," E "]" => subfieldIntegers F E

/-- The field unit defined by a nonzero element of the extension integer ring. -/
def subfieldIntegerUnit {a : 𝒪ₑ[F,E]} (ha : a ≠ 0) : Eˣ :=
  Units.mk0 (a : E) (fun h => ha (Subtype.ext h))

@[simp] theorem subfieldIntegerUnit_val {a : 𝒪ₑ[F,E]} (ha : a ≠ 0) :
    (subfieldIntegerUnit E ha : E) = a := rfl

/-- The field unit defined by the image of a nonzero base integer. -/
def baseIntegerUnit {a : 𝒪[F]} (ha : a ≠ 0) : Eˣ :=
  Units.mk0 (algebraMap F E (a : F)) (fun h =>
    ha (Subtype.ext ((algebraMap F E).injective (h.trans (map_zero _).symm))))

@[simp] theorem baseIntegerUnit_val {a : 𝒪[F]} (ha : a ≠ 0) :
    (baseIntegerUnit E ha : E) = algebraMap F E (a : F) := rfl

/-- The homomorphism from the extension's integer units to its field units. -/
abbrev subfieldIntegerUnits : 𝒪ₑ[F,E]ˣ →* Eˣ :=
  Units.map (algebraMap 𝒪ₑ[F,E] E).toMonoidHom

variable [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E]

/-- Every nonzero field element has a uniformizer-power decomposition with a unit. -/
theorem subfieldUnit_factorization {ϖ : 𝒪ₑ[F,E]} (hϖ : Irreducible ϖ) (a : Eˣ) :
    ∃ (n : ℤ) (u : 𝒪ₑ[F,E]ˣ),
      a = subfieldIntegerUnits E u * subfieldIntegerUnit E hϖ.ne_zero ^ n := by
  obtain ⟨n, u, hu⟩ := exists_units_eq_smul_zpow_of_irreducible hϖ (Units.ne_zero a)
  refine ⟨n, u, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  change (a : E) = ((u : 𝒪ₑ[F,E]) : E) * (ϖ : E) ^ n
  rw [Units.smul_def, Algebra.smul_def] at hu
  exact hu

namespace LatticeChain

variable {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

include 𝓛 hE in
omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
/-- The extension integer ring embeds in one lattice by evaluation on a nonzero vector. -/
theorem finite_subfieldIntegers [IsNoetherianRing 𝒪[F]] : Module.Finite 𝒪[F] 𝒪ₑ[F,E] := by
  obtain ⟨v, hv, hv'⟩ := (SetLike.lt_iff_le_and_exists.mp (𝓛.lattice_succ_lt 0)).2
  have hv₀ : v ≠ 0 := by
    rintro rfl
    exact hv' (zero_mem _)
  have := (Module.Finite.iff_fg).mpr (𝓛.fg_lattice 0)
  let f : 𝒪ₑ[F,E] →ₗ[𝒪[F]] 𝓛.lattice 0 :=
    { toFun := fun a => ⟨(a : E) • v, 𝓛.subfieldInteger_smul_mem E hE 0 a hv⟩
      map_add' := fun a b => Subtype.ext (add_smul (a : E) (b : E) v)
      map_smul' := fun c a => Subtype.ext (smul_assoc c (a : E) v) }
  exact Module.Finite.of_injective f (fun _ _ h => Subtype.ext
    (smul_left_injective E hv₀ (congrArg (fun z : 𝓛.lattice 0 => (z : V)) h)))

omit [IsDiscreteValuationRing 𝒪ₑ[F,E]] [IsFractionRing 𝒪ₑ[F,E] E] in
/-- The shift reads the power of the extension uniformizer in a field unit. -/
theorem fieldShift_eq_mul_of_factorization {a : Eˣ} {ϖ : 𝒪ₑ[F,E]} (hϖ : ϖ ≠ 0)
    {n : ℤ} {u : 𝒪ₑ[F,E]ˣ}
    (ha : a = subfieldIntegerUnits E u * subfieldIntegerUnit E hϖ ^ n) :
    (𝓛.fieldShift E hE a).toAdd =
      (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ)).toAdd * n := by
  rw [ha, map_mul, map_zpow]
  change (𝓛.fieldShift E hE (subfieldIntegerUnits E u)).toAdd +
    ((𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ)) ^ n).toAdd = _
  rw [𝓛.fieldShift_integerUnit E hE u, zero_add, Int.toAdd_zpow]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

include 𝓛 hE in
omit [IsFractionRing 𝒪ₑ[F,E] E] in
/-- The ramification index is nonzero because the base uniformizer shifts by a positive period. -/
theorem subfieldRamificationIndex_pos : 0 < subfieldRamificationIndex F E := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪ₑ[F,E]
  have h := 𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ
  by_contra! he
  have hzero : subfieldRamificationIndex F E = 0 := Nat.eq_zero_of_le_zero he
  rw [hzero, Nat.cast_zero, mul_zero] at h
  exact 𝓛.period_pos.ne' (by exact_mod_cast h.symm)

omit [IsFractionRing 𝒪ₑ[F,E] E] in
/-- Every uniformizer of the extension gives the same translation. -/
theorem fieldShift_uniformizers_eq {ϖ ϖ' : 𝒪ₑ[F,E]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ.ne_zero)).toAdd =
      (𝓛.fieldShift E hE (subfieldIntegerUnit E hϖ'.ne_zero)).toAdd := by
  have he : (subfieldRamificationIndex F E : ℤ) ≠ 0 := by
    exact_mod_cast (𝓛.subfieldRamificationIndex_pos E hE).ne'
  apply mul_right_cancel₀ he
  exact (𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ).trans
    (𝓛.fieldShift_uniformizer_mul_ramification E hE hϖ').symm

include 𝓛 hE in
omit [IsFractionRing 𝒪ₑ[F,E] E] in
/-- The power in a uniformizer-power decomposition agrees with the published valuation. -/
theorem subfieldNormalizedValuation_eq_of_factorization {a : Eˣ} {ϖ : 𝒪ₑ[F,E]}
    (hϖ : Irreducible ϖ) {n : ℤ} {u : 𝒪ₑ[F,E]ˣ}
    (ha : a = subfieldIntegerUnits E u * subfieldIntegerUnit E hϖ.ne_zero ^ n) :
    subfieldNormalizedValuation F E (a : E) = (n : WithTop ℤ) := by
  classical
  have hset : {m : ℤ | ∃ π : 𝒪ₑ[F,E],
      π ≠ 0 ∧ Ideal.span ({π} : Set 𝒪ₑ[F,E]) = subfieldMaximalIdeal F E ∧
      ∃ w : 𝒪ₑ[F,E]ˣ, (a : E) = (π : E) ^ m * ((w : 𝒪ₑ[F,E]) : E)} = {n} := by
    ext m
    constructor
    · rintro ⟨π, _, hspan, w, hw⟩
      have hπ : Irreducible π := (irreducible_iff_uniformizer π).mpr
        ((subfieldMaximalIdeal_eq F E).symm.trans hspan.symm)
      have hw' : a = subfieldIntegerUnits E w * subfieldIntegerUnit E hπ.ne_zero ^ m := by
        apply Units.ext
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
        exact hw.trans (mul_comm _ _)
      have h := (𝓛.fieldShift_eq_mul_of_factorization E hE hπ.ne_zero hw').symm.trans
        (𝓛.fieldShift_eq_mul_of_factorization E hE hϖ.ne_zero ha)
      rw [𝓛.fieldShift_uniformizers_eq E hE hπ hϖ] at h
      exact Set.mem_singleton_iff.mpr
        (mul_left_cancel₀ (𝓛.fieldShift_uniformizer_pos E hE hϖ).ne' h)
    · intro hm
      obtain rfl := Set.mem_singleton_iff.mp hm
      refine ⟨ϖ, hϖ.ne_zero, hϖ.maximalIdeal_eq.symm.trans (subfieldMaximalIdeal_eq F E).symm, u, ?_⟩
      have hc := congrArg (fun z : Eˣ => (z : E)) ha
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val] at hc
      exact hc.trans (mul_comm _ _)
  rw [subfieldNormalizedValuation, ite_eq_right (Units.ne_zero a), hset, csSup_singleton]

/-- A field unit of shift zero comes from an integer-ring unit. -/
theorem exists_integerUnit_of_fieldShift_zero {a : Eˣ} (ha : (𝓛.fieldShift E hE a).toAdd = 0) :
    ∃ u : 𝒪ₑ[F,E]ˣ, a = subfieldIntegerUnits E u := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪ₑ[F,E]
  obtain ⟨n, u, hu⟩ := subfieldUnit_factorization E hϖ a
  have h := 𝓛.fieldShift_eq_mul_of_factorization E hE hϖ.ne_zero hu
  rw [ha, eq_comm, mul_eq_zero] at h
  have hn := h.resolve_left (𝓛.fieldShift_uniformizer_pos E hE hϖ).ne'
  exact ⟨u, by simpa only [hn, zpow_zero, mul_one] using hu⟩

end LatticeChain

end Langlands.BushnellKutzko
