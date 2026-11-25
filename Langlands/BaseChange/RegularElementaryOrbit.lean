import Langlands.BaseChange.RegularElementaryTests
import Langlands.BaseChange.StrictTwistedDiagonals
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof

/-! # Orbit preimages of the strict elementary supports -/

noncomputable section

namespace Langlands.BaseChange

open Matrix Set Langlands.Unramified
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val torus)
open ClassFieldTheory.Local
open LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer

universe u v

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

attribute [local instance] heckeFieldValuativeRel

theorem entrywiseAut_diagonalUnits {F : Type u} [CommRing F] {E : Type v}
    [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) (a : Fin n → Eˣ) :
    entrywiseAut σ n (diagonalUnits a) =
      diagonalUnits (fun i => Units.map σ.toMonoidHom (a i)) := by
  apply Units.ext
  change (diagonalUnits a).val.map σ.toRingHom = _
  rw [diagonalUnits_val, diagonalUnits_val, diagonal_map (map_zero σ.toRingHom)]
  rfl

theorem baseChange_diagonalUnits {F : Type u} [Field F] {E : Type v}
    [Field E] [Algebra F E] (a : Fin n → Fˣ) :
    baseChange F E n (diagonalUnits a) =
      diagonalUnits (fun i => Units.map (algebraMap F E) (a i)) := by
  apply Units.ext
  change (diagonalUnits a).val.map (algebraMap F E) = _
  rw [diagonalUnits_val, diagonalUnits_val, diagonal_map (map_zero (algebraMap F E))]
  rfl

section Support

variable (E : PadicField.{v} p) {r : ℕ} (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)
  (π : E.Carrierˣ) (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
  (ν : Fin (r + 1) → ℤ)

local notation "D" => E.canonicalTopologicalData

include hπ in
theorem mem_elementaryDiagonalTuples_iff (a : Fin (r + 1) → E.Carrierˣ) :
    a ∈ elementaryDiagonalTuples E π ν ↔ ∀ i, (D).ord (a i : E.Carrier) = ν i := by
  constructor
  · intro ha i
    obtain ⟨b, hb, hb'⟩ := ha i (Set.mem_univ _)
    rw [← hb', Units.val_mul, (D).ord_mul (Units.ne_zero _) b.ne_zero,
      Units.val_zpow_eq_zpow_val, (D).ord_zpow, hπ, mul_one,
      (mem_unitSubgroup_iff_ord_eq_zero E D b).mp hb, add_zero]
  · intro ha i _
    let z := π ^ ν i
    refine ⟨z⁻¹ * a i, (mem_unitSubgroup_iff_ord_eq_zero E D _).2 ?_, mul_inv_cancel_left _ _⟩
    rw [Units.val_mul, (D).ord_mul (Units.ne_zero _) (a i).ne_zero, ha]
    have hz : z⁻¹ = π ^ (-(ν i)) := (zpow_neg π (ν i)).symm
    rw [hz]
    rw [Units.val_zpow_eq_zpow_val, (D).ord_zpow, hπ, mul_one, neg_add_cancel]

include hπ in
/-- The orbit-map preimage of the strict upper support is the diagonal
subgroup times the spherical subgroup. -/
theorem twistedConj_mem_regularElementarySupport_iff
    (hν : StrictAnti ν) {a : Fin (r + 1) → E.Carrierˣ}
    (ha : ∀ i, (D).ord (a i : E.Carrier) = ν i) (x : GeneralLinear (r + 1) E.Carrier) :
    x⁻¹ * diagonalUnits a * entrywiseAut τ (r + 1) x ∈ regularElementarySupport E τ π ν ↔
      ∃ t : Fin (r + 1) → E.Carrierˣ, ∃ k ∈ sphericalOpenSubgroup E r, x = diagonalUnits t * k := by
  constructor
  · rintro ⟨k, hk, b, hb, h⟩
    have hEq : (x * k⁻¹)⁻¹ * diagonalUnits a * entrywiseAut τ (r + 1) (x * k⁻¹) =
        diagonalUnits b := by
      rw [_root_.mul_inv_rev, inv_inv, map_mul, map_inv]
      calc
        _ = k * (x⁻¹ * diagonalUnits a * entrywiseAut τ (r + 1) x) *
              (entrywiseAut τ (r + 1) k)⁻¹ := by group
        _ = _ := by rw [← h]; group
    have hb' := (mem_elementaryDiagonalTuples_iff E π hπ ν b).1 hb
    obtain ⟨t, ht⟩ := exists_diagonalUnits_of_strict_twistedConj E τ
      (fun i => (ha i).trans (hb' i).symm) (by simpa only [ha] using hν.injective) hEq
    exact ⟨t, k, hk, by simpa using congrArg (· * k) ht⟩
  · rintro ⟨t, k, hk, rfl⟩
    let b : Fin (r + 1) → E.Carrierˣ := fun i => (t i)⁻¹ * a i * Units.map τ.toMonoidHom (t i)
    have hb : b ∈ elementaryDiagonalTuples E π ν := by
      apply (mem_elementaryDiagonalTuples_iff E π hπ ν b).2
      intro i
      change (D).ord ((↑((t i)⁻¹ * a i) : E.Carrier) * τ (t i : E.Carrier)) = _
      rw [(D).ord_mul (Units.ne_zero _) ((map_ne_zero τ).mpr (t i).ne_zero),
        Units.val_mul, (D).ord_mul (Units.ne_zero _) (a i).ne_zero, ha,
        LocalClassField.UniverseZero.ord_eq_of_algEquiv τ D D, Units.val_inv_eq_inv_val, (D).ord_inv]
      abel
    refine ⟨k, hk, b, hb, ?_⟩
    have hb' : diagonalUnits b = (diagonalUnits t)⁻¹ * diagonalUnits a *
        entrywiseAut τ (r + 1) (diagonalUnits t) := by
      rw [entrywiseAut_diagonalUnits, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hb', _root_.mul_inv_rev, map_mul]
    simp only [mul_assoc]

end Support

section Integral

variable (F : PadicField.{u} p) (E : PadicField.{v} p) {r : ℕ}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)

theorem diagonalUnits_mem_sphericalOpenSubgroup_iff (a : Fin (r + 1) → E.Carrierˣ) :
    diagonalUnits a ∈ sphericalOpenSubgroup E r ↔
      ∀ i, E.canonicalTopologicalData.ord (a i : E.Carrier) = 0 := by
  let D := E.canonicalTopologicalData
  let v := ValuativeRel.valuation E.Carrier
  change diagonalUnits a ∈ Conductor.integralSubgroup v.integer r ↔ _
  constructor
  · intro ha i
    obtain ⟨hx, hy⟩ := (Conductor.mem_integralSubgroup v.integer r _).mp ha
    have hx' : (a i : E.Carrier) ∈ v.integer := by
      simpa only [diagonalUnits_val, diagonal_apply_eq] using hx i i
    have hy' : ((a i)⁻¹ : E.Carrierˣ).val ∈ v.integer := by
      rw [← map_inv diagonalUnits] at hy
      simpa only [diagonalUnits_val, diagonal_apply_eq, Pi.inv_apply] using hy i i
    have h₁ := (Valuation.mem_integer_iff v _).1 hx'
    have h₂ := (Valuation.mem_integer_iff v _).1 hy'
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h₂
    apply (mem_unitSubgroup_iff_ord_eq_zero E D _).mp
    exact (Valuation.mem_unitGroup_iff E.Carrier v _).mpr
      (le_antisymm h₁ ((inv_le_one₀ (pos_iff_ne_zero.mpr
        ((Valuation.ne_zero_iff v).mpr (a i).ne_zero))).mp h₂))
  · intro h
    apply GeneralLinear.Iwasawa.diagonalUnits_mem
    intro i
    exact (Valuation.mem_unitGroup_iff E.Carrier v _).mp
      ((mem_unitSubgroup_iff_ord_eq_zero E D _).mpr (h i))

include he in
theorem ord_algebraMap_of_elementary_unramified (x : F.Carrier) :
    E.canonicalTopologicalData.ord (algebraMap F.Carrier E.Carrier x) =
      F.canonicalTopologicalData.ord x := by
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  have h := ramificationIndex_mul_ord_algebraMap (K := F) (M := E) T S x
  change (T.ramificationIndex : ℤ) * S.ord (algebraMap F.Carrier E.Carrier x) =
    (S.ramificationIndex : ℤ) * T.ord x at h
  rw [he] at h
  exact mul_left_cancel₀ (by exact_mod_cast T.ramificationIndex_pos.ne') h

include he in
/-- Every upper diagonal is the scalar extension of a lower diagonal
times an integral upper diagonal. -/
theorem exists_diagonal_baseChange_mul_spherical (t : Fin (r + 1) → E.Carrierˣ) :
    ∃ a : Fin (r + 1) → F.Carrierˣ, ∃ k ∈ sphericalOpenSubgroup E r,
      diagonalUnits t = baseChange F.Carrier E.Carrier (r + 1) (diagonalUnits a) * k := by
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  let a (i : Fin (r + 1)) : F.Carrierˣ := T.uniformizerUnit ^ S.ord (t i : E.Carrier)
  let z (i : Fin (r + 1)) : E.Carrierˣ := Units.map (algebraMap F.Carrier E.Carrier) (a i)
  let b (i : Fin (r + 1)) := (z i)⁻¹ * t i
  have hz (i : Fin (r + 1)) : S.ord (z i : E.Carrier) = S.ord (t i : E.Carrier) := by
    change S.ord (algebraMap F.Carrier E.Carrier (a i : F.Carrier)) = _
    rw [ord_algebraMap_of_elementary_unramified F E he]
    change T.ord (↑(T.uniformizerUnit ^ S.ord (t i : E.Carrier)) : F.Carrier) = _
    rw [Units.val_zpow_eq_zpow_val, T.ord_zpow, T.uniformizerUnit_val, T.ord_uniformizer, mul_one]
  have hb : diagonalUnits b ∈ sphericalOpenSubgroup E r := by
    apply (diagonalUnits_mem_sphericalOpenSubgroup_iff E b).2
    intro i
    change S.ord (↑((z i)⁻¹ * t i) : E.Carrier) = 0
    rw [Units.val_mul, S.ord_mul (Units.ne_zero _) (t i).ne_zero,
      Units.val_inv_eq_inv_val, S.ord_inv, hz, neg_add_cancel]
  refine ⟨a, diagonalUnits b, hb, ?_⟩
  rw [baseChange_diagonalUnits, ← map_mul]
  exact congrArg (fun t : Fin (r + 1) → E.Carrierˣ => diagonalUnits t) (funext fun i => by
    change t i = z i * ((z i)⁻¹ * t i)
    rw [mul_inv_cancel_left])

end Integral

section Norm

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- The ordered matrix norm on a diagonal is the diagonal of the field norms. -/
theorem cyclicNorm_diagonalUnits_eq (hσ : IsCyclicAlgebra σ l) (a : Fin n → Eˣ) :
    cyclicNorm σ l (diagonalUnits a) =
      baseChange F E n (diagonalUnits (fun i => Units.map (Algebra.norm F) (a i))) := by
  let b (k : ℕ) (i : Fin n) := Units.map ((σ ^ k).toMonoidHom) (a i)
  have hprod (k : ℕ) : cyclicNorm σ k (diagonalUnits a) =
      diagonalUnits (fun i => ((List.range k).map fun j => b j i).prod) := by
    induction k with
    | zero =>
      simp only [cyclicNorm_zero, List.range_zero, List.map_nil, List.prod_nil]
      exact (map_one (diagonalUnits : (Fin n → Eˣ) →* GeneralLinear n E)).symm
    | succ k ih =>
      rw [cyclicNorm_succ, ih, entrywiseAut_diagonalUnits, ← map_mul]
      congr 1
      funext i
      simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, b, Pi.mul_apply]
  rw [hprod, baseChange_diagonalUnits]
  congr 1
  funext i
  have hRank (k : ℕ) :
      GeneralLinear.determinant (cyclicNorm σ k (GeneralLinear.scalar (n := 1) (a i))) =
        ((List.range k).map fun j => b j i).prod := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [cyclicNorm_succ, map_mul, ih,
        List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
      congr 1
      apply Units.ext
      change ((entrywiseAut (σ ^ k) 1 (GeneralLinear.scalar (n := 1) (a i))).val).det = _
      simp [GeneralLinear.scalar, b]
  apply Units.ext
  rw [← hRank]
  have ha : GeneralLinear.determinant (GeneralLinear.scalar (n := 1) (a i)) = a i := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) (a i)) = _
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]
  have h := hσ.determinant_cyclicNorm (GeneralLinear.scalar (n := 1) (a i))
  rw [ha] at h
  exact h

end Norm

end Langlands.BaseChange
