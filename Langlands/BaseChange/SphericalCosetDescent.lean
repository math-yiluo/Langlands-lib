import Langlands.BaseChange.IntegralMatrixDescent
import Langlands.BaseChange.UnramifiedCyclicIntegers
import Langlands.Representation.Unramified.HeckeOperators

/-! Fixed spherical cosets for an unramified cyclic extension. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix Correspondence IsLocalRing PadicField.TopologicalData

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

local notation "T" => F.canonicalTopologicalData
local notation "S" => E.canonicalTopologicalData
local instance : Algebra (T).Integers (S).Integers := relativeIntegerAlgebra T S

/-- Base change preserves and reflects spherical subgroup membership. -/
theorem baseChange_mem_sphericalSubgroup_iff {r : ℕ}
    (x : GeneralLinear (r + 1) F.Carrier) :
    baseChange F.Carrier E.Carrier (r + 1) x ∈ sphericalSubgroup E r ↔
      x ∈ sphericalSubgroup F r := by
  change _ ∈ Conductor.integralSubgroup (S).Integers r ↔
    x ∈ Conductor.integralSubgroup (T).Integers r
  rw [Conductor.mem_integralSubgroup, Conductor.mem_integralSubgroup, ← map_inv]
  simp only [baseChange_apply_apply, relative_mem_integers_iff T S]

section IntegralActions

variable (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) {n : ℕ}

local notation "ι" => GeneralLinearGroup.map
  (Subring.subtype (PadicField.TopologicalData.Integers S))

private theorem map_entrywiseAut (g : GeneralLinear n (S).Integers) :
    ι (entrywiseAut (canonicalIntegerAut F E σ) n g) = entrywiseAut σ n (ι g) := by
  apply GeneralLinearGroup.ext
  intro i j
  rfl

private theorem map_cyclicNorm (l : ℕ) (g : GeneralLinear n (S).Integers) :
    ι (cyclicNorm (canonicalIntegerAut F E σ) l g) = cyclicNorm σ l (ι g) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cyclicNorm_succ, cyclicNorm_succ, map_mul, ih, ← map_pow,
      map_entrywiseAut F E (σ ^ l)]

/-- Entrywise Galois action preserves the spherical subgroup. -/
theorem entrywiseAut_mem_sphericalSubgroup {r : ℕ} {x : GeneralLinear (r + 1) E.Carrier}
    (hx : x ∈ sphericalSubgroup E r) : entrywiseAut σ (r + 1) x ∈ sphericalSubgroup E r := by
  change x ∈ (GeneralLinearGroup.map (S).Integers.subtype).range at hx
  obtain ⟨g, rfl⟩ := hx
  exact ⟨entrywiseAut (canonicalIntegerAut F E σ) (r + 1) g, map_entrywiseAut F E σ g⟩

/-- A basis of a σ-stable spherical coset can be chosen over the base field. -/
theorem exists_baseChange_mul_spherical_of_fixed {l r : ℕ}
    (hσ : IsCyclicAlgebra σ l) (he : (S).ramificationIndex = (T).ramificationIndex)
    (x : GeneralLinear (r + 1) E.Carrier)
    (hx : x⁻¹ * entrywiseAut σ (r + 1) x ∈ sphericalSubgroup E r) :
    ∃ (y : GeneralLinear (r + 1) F.Carrier) (k : GeneralLinear (r + 1) E.Carrier),
      k ∈ sphericalSubgroup E r ∧ baseChange F.Carrier E.Carrier (r + 1) y = x * k := by
  let σ₀ := canonicalIntegerAut F E σ
  have hperiod : σ₀ ^ l = 1 := by
    rw [← map_pow, hσ.pow_eq_one, map_one]
  obtain ⟨a, ha⟩ := exists_integer_distinct_conjugates F E hσ he
  have hsep : Pairwise fun i j : Fin l => IsUnit ((σ₀ ^ (i : ℕ)) a - (σ₀ ^ (j : ℕ)) a) := by
    intro i j hij
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_sub, sub_ne_zero]
    simpa only [σ₀, ← map_pow] using ha.ne hij
  change x⁻¹ * entrywiseAut σ (r + 1) x ∈ (GeneralLinearGroup.map (S).Integers.subtype).range at hx
  obtain ⟨g, hg⟩ := hx
  have hnorm : cyclicNorm σ₀ l g = 1 := by
    apply Conductor.integral_map_injective (S).Integers r
    change ι (cyclicNorm (canonicalIntegerAut F E σ) l g) = ι 1
    rw [map_one, map_cyclicNorm F E σ, hg, ← mul_one x⁻¹,
      cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply]
    simp [cyclicNorm]
  obtain ⟨c, hc⟩ := exists_integral_twistedConj_eq_one σ₀ hσ.pos hperiod g hnorm a hsep
  have hmul : g * entrywiseAut σ₀ (r + 1) c = c := by
    calc
      g * entrywiseAut σ₀ (r + 1) c = c * (c⁻¹ * g * entrywiseAut σ₀ (r + 1) c) := by group
      _ = c := by rw [hc, mul_one]
  let k := ι c
  have hk : (x⁻¹ * entrywiseAut σ (r + 1) x) * entrywiseAut σ (r + 1) k = k := by
    have h := congrArg (GeneralLinearGroup.map (S).Integers.subtype) hmul
    rw [map_mul, map_entrywiseAut F E σ, hg] at h
    exact h
  have hfixed : entrywiseAut σ (r + 1) (x * k) = x * k := by
    calc
      entrywiseAut σ (r + 1) (x * k) =
          x * ((x⁻¹ * entrywiseAut σ (r + 1) x) * entrywiseAut σ (r + 1) k) := by
        rw [map_mul]
        group
      _ = x * k := congrArg (x * ·) hk
  obtain ⟨y, hy⟩ := exists_baseChange_eq_of_entrywiseAut_eq hσ.2.2.2.2 hfixed
  exact ⟨y, k, ⟨c, rfl⟩, hy⟩

end IntegralActions

/-- Coefficient extension on cosets of the spherical subgroup. -/
def sphericalCosetBaseChange (r : ℕ) :
    (GeneralLinear (r + 1) F.Carrier ⧸ sphericalSubgroup F r) →
      (GeneralLinear (r + 1) E.Carrier ⧸ sphericalSubgroup E r) :=
  Quotient.map' (baseChange F.Carrier E.Carrier (r + 1)) fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul, baseChange_mem_sphericalSubgroup_iff F E]
    exact h

@[simp] theorem sphericalCosetBaseChange_mk {r : ℕ} (x : GeneralLinear (r + 1) F.Carrier) :
    sphericalCosetBaseChange F E r (QuotientGroup.mk x) =
      QuotientGroup.mk (baseChange F.Carrier E.Carrier (r + 1) x) := rfl

theorem sphericalCosetBaseChange_injective (r : ℕ) :
    Function.Injective (sphericalCosetBaseChange F E r) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with | H x =>
  induction b using QuotientGroup.induction_on with | H y =>
  rw [sphericalCosetBaseChange_mk, sphericalCosetBaseChange_mk, QuotientGroup.eq,
    ← map_inv, ← map_mul, baseChange_mem_sphericalSubgroup_iff F E] at hab
  exact QuotientGroup.eq.mpr hab

/-- The extension coset of `x` arises over `F` exactly when it is fixed by `σ`. -/
theorem mem_range_sphericalCosetBaseChange_iff {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l r : ℕ}
    (hσ : IsCyclicAlgebra σ l) (he : (S).ramificationIndex = (T).ramificationIndex)
    (x : GeneralLinear (r + 1) E.Carrier) :
    QuotientGroup.mk x ∈ Set.range (sphericalCosetBaseChange F E r) ↔
      x⁻¹ * entrywiseAut σ (r + 1) x ∈ sphericalSubgroup E r := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with | H y =>
    rw [sphericalCosetBaseChange_mk, QuotientGroup.eq] at hq
    let b := baseChange F.Carrier E.Carrier (r + 1) y
    change b⁻¹ * x ∈ sphericalSubgroup E r at hq
    have hq' := entrywiseAut_mem_sphericalSubgroup F E σ hq
    rw [map_mul, map_inv, entrywiseAut_baseChange] at hq'
    change b⁻¹ * entrywiseAut σ (r + 1) x ∈ sphericalSubgroup E r at hq'
    have h := (sphericalSubgroup E r).mul_mem ((sphericalSubgroup E r).inv_mem hq) hq'
    convert h using 1
    group
  · intro hx
    obtain ⟨y, k, hk, hy⟩ := exists_baseChange_mul_spherical_of_fixed F E σ hσ he x hx
    refine ⟨QuotientGroup.mk y, ?_⟩
    rw [sphericalCosetBaseChange_mk, hy]
    symm
    exact QuotientGroup.eq.mpr (by simpa using hk)

end Langlands.BaseChange
