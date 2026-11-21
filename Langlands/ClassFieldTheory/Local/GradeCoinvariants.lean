import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Mathlib.Algebra.Polynomial.Roots

/-! # Positive unit grades and coinvariants of a Frobenius lift -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open IsLocalRing Ramification.HerbrandBridge

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)
variable (e : T.Integers ≃+* T.Integers)

private theorem map_mem_congruenceUnits {n : ℕ} {u : T.Integersˣ} (hu : u ∈ T.congruenceUnits n) :
    Units.map e.toMonoidHom u ∈ T.congruenceUnits n := by
  rw [T.mem_congruenceUnits_iff] at hu ⊢
  change e (u : T.Integers) - 1 ∈ maximalIdeal T.Integers ^ n
  rw [← map_one e, ← map_sub]
  exact (ringEquiv_mem_maximalIdeal_pow_iff e n _).mpr hu

private def congruenceUnitsMap (n : ℕ) : T.congruenceUnits n →* T.congruenceUnits n :=
  ((Units.map e.toMonoidHom).comp (T.congruenceUnits n).subtype).codRestrict _
    (fun x => T.map_mem_congruenceUnits e x.property)

/-- An integer-ring automorphism acts on each actual unit level. -/
def unitFiltrationMap (n : ℕ) : T.unitFiltration n →* T.unitFiltration n :=
  (T.congruenceUnitsEquivFiltration n).toMonoidHom.comp
    ((T.congruenceUnitsMap e n).comp (T.congruenceUnitsEquivFiltration n).symm.toMonoidHom)

@[simp] theorem filtrationIntegerUnit_unitFiltrationMap (n : ℕ) (x : T.unitFiltration n) :
    T.filtrationIntegerUnit n (T.unitFiltrationMap e n x) =
      Units.map e.toMonoidHom (T.filtrationIntegerUnit n x) := by
  change ((T.congruenceUnitsEquivFiltration n).symm ((T.congruenceUnitsEquivFiltration n)
    (T.congruenceUnitsMap e n ((T.congruenceUnitsEquivFiltration n).symm x)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The induced action on the actual successive quotient of unit groups. -/
def unitGradeMap (n : ℕ) : T.GradedUnits n →* T.GradedUnits n :=
  QuotientGroup.lift _ ((T.gradedUnitProjection n).comp (T.unitFiltrationMap e n)) (by
    intro x hx
    apply (QuotientGroup.eq_one_iff (T.unitFiltrationMap e n x)).mpr
    change (T.unitFiltrationMap e n x).val ∈ T.unitFiltration (n + 1)
    rw [← T.filtrationIntegerUnit_mem_iff, filtrationIntegerUnit_unitFiltrationMap]
    exact T.map_mem_congruenceUnits e ((T.filtrationIntegerUnit_mem_iff n (n + 1) x).mpr hx))

@[simp] theorem unitGradeMap_projection (n : ℕ) (x : T.unitFiltration n) :
    T.unitGradeMap e n (T.gradedUnitProjection n x) =
      T.gradedUnitProjection n (T.unitFiltrationMap e n x) := rfl

/-- The coefficient changes by the residue automorphism times a constant
factor, the residue of the uniformizer ratio to the power `n`. -/
theorem unitGradeMap_coordinates {n : ℕ} (hn : 0 < n) (π : F.Carrier) (hπ : T.ord π = 1) :
    ∃ c : T.ResidueField, ∀ x : T.GradedUnits n,
      (T.gradedUnitsPositiveEquiv π hπ n hn (T.unitGradeMap e n x)).toAdd =
        c * IsLocalRing.ResidueField.mapAut e ((T.gradedUnitsPositiveEquiv π hπ n hn x).toAdd) := by
  let t := T.coordinateUniformizer π hπ
  have ht : t ∈ maximalIdeal T.Integers ^ 1 := by
    rw [T.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ, pow_one]
  obtain ⟨a, ha⟩ := (T.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ 1 _).mp
    ((ringEquiv_mem_maximalIdeal_pow_iff e 1 t).mpr ht)
  rw [pow_one] at ha
  refine ⟨T.residue a ^ n, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (T.gradedUnitKernel n) x
  change (T.gradedUnitsPositiveEquiv π hπ n hn (T.unitGradeMap e n (T.gradedUnitProjection n x))).toAdd =
    _ * IsLocalRing.ResidueField.mapAut e ((T.gradedUnitsPositiveEquiv π hπ n hn
      (T.gradedUnitProjection n x)).toAdd)
  rw [unitGradeMap_projection, gradedUnitsPositiveEquiv_projection, gradedUnitsPositiveEquiv_projection]
  change T.residue (T.unitCoefficient π hπ n (T.unitFiltrationMap e n x)) = _
  have hc : T.unitCoefficient π hπ n (T.unitFiltrationMap e n x) =
      a ^ n * e (T.unitCoefficient π hπ n x) := by
    apply mul_left_cancel₀ (pow_ne_zero n (T.coordinateUniformizer_integer_ne_zero π hπ))
    rw [T.coordinateUniformizer_pow_mul_coefficient, filtrationIntegerUnit_unitFiltrationMap]
    have h := congrArg e (T.coordinateUniformizer_pow_mul_coefficient π hπ n x)
    change e (t ^ n * T.unitCoefficient π hπ n x) = e ((T.filtrationIntegerUnit n x : T.Integers) - 1) at h
    rw [map_mul, map_pow, ha, mul_pow, mul_assoc, map_sub, map_one] at h
    exact h.symm
  rw [hc, map_mul, map_pow]
  rfl

private theorem card_scaled_power_fixed_le {k : Type*} [Field k] (q : ℕ) (hq : 1 < q) (c : k) :
    Nat.card {x : k // c * x ^ q = x} ≤ q := by
  classical
  let P : Polynomial k := Polynomial.C c * Polynomial.X ^ q - Polynomial.X
  have hp : P ≠ 0 := by
    intro h
    have hh := congrArg (fun f : Polynomial k => f.coeff 1) h
    simp [P, hq.ne] at hh
  have hdeg : P.natDegree ≤ q := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · by_cases hc : c = 0
      · simp [hc]
      · rw [Polynomial.natDegree_C_mul_X_pow _ _ hc]
    · simpa using hq.le
  let f : {x : k // c * x ^ q = x} → P.roots.toFinset := fun x => ⟨x.val, by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    simp [P, Polynomial.IsRoot.def, x.property]⟩
  calc
    _ ≤ Nat.card ↥P.roots.toFinset := Nat.card_le_card_of_injective f
      (fun x y h => Subtype.ext (congrArg (fun z : ↥P.roots.toFinset => z.val) h))
    _ ≤ P.roots.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ q := hdeg

/-- If the residue action is the `q`-power Frobenius, the fixed subgroup on
any positive unit grade has at most `q` elements. -/
theorem card_unitGradeMap_fixed_le {n q : ℕ} (hn : 0 < n) (hq : 1 < q)
    (he : ∀ x : T.ResidueField, IsLocalRing.ResidueField.mapAut e x = x ^ q) :
    Nat.card {x : T.GradedUnits n // T.unitGradeMap e n x = x} ≤ q := by
  let i := T.gradedUnitsPositiveEquiv T.uniformizer T.ord_uniformizer n hn
  obtain ⟨c, hc⟩ := T.unitGradeMap_coordinates e hn T.uniformizer T.ord_uniformizer
  let f : {x : T.GradedUnits n // T.unitGradeMap e n x = x} → {x : T.ResidueField // c * x ^ q = x} :=
    fun x => ⟨(i x).toAdd, by
      have hx := hc x.val
      rw [he, x.property] at hx
      exact hx.symm⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (i.injective (Multiplicative.toAdd.injective (congrArg Subtype.val h)))
  let : Finite T.ResidueField := T.finite_residueField
  exact (Nat.card_le_card_of_injective f hf).trans (card_scaled_power_fixed_le q hq c)

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField.GradeCoinvariants

/-- A surjective invariant map out of a finite abelian group realizes the
coinvariant quotient when its target has at least as many elements as the
fixed subgroup of the endomorphism. Invariant characters therefore descend. -/
theorem exists_hom_factor_of_fixed_card_le
    {G H D : Type*} [CommGroup G] [CommGroup H] [CommGroup D] [Finite G] [Finite H]
    (s : G →* G) (f : G →* H) (θ : G →* D)
    (hf : Function.Surjective f) (hf_s : ∀ x, f (s x) = f x) (hθ_s : ∀ x, θ (s x) = θ x)
    (hc : Nat.card {x : G // s x = x} ≤ Nat.card H) :
    ∃ η : H →* D, η.comp f = θ := by
  let δ := s / MonoidHom.id G
  let R := δ.range
  have hR (x : G) : x ∈ R → f x = 1 := by
    rintro ⟨y, rfl⟩
    change f (s y / y) = 1
    rw [map_div, hf_s, div_self']
  have hθ (x : G) : x ∈ R → θ x = 1 := by
    rintro ⟨y, rfl⟩
    change θ (s y / y) = 1
    rw [map_div, hθ_s, div_self']
  let fQ := QuotientGroup.lift R f hR
  have hfs : Function.Surjective fQ := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk' R x, rfl⟩
  have hker : Nat.card δ.ker = Nat.card {x : G // s x = x} :=
    Nat.card_congr (Equiv.subtypeEquivProp (funext fun x => propext (div_eq_one : s x / x = 1 ↔ s x = x)))
  have hq : Nat.card (G ⧸ R) = Nat.card δ.ker := by
    have h1 := R.card_eq_card_quotient_mul_card_subgroup
    have h2 := δ.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv, mul_comm] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.symm.trans h2)
  let e := MulEquiv.ofBijective fQ (hfs.bijective_of_nat_card_le (hq ▸ hker.symm ▸ hc))
  refine ⟨(QuotientGroup.lift R θ hθ).comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  change QuotientGroup.lift R θ hθ (e.symm (e (QuotientGroup.mk' R x))) = θ x
  rw [MulEquiv.symm_apply_apply]
  rfl

end Langlands.LocalClassField.GradeCoinvariants
