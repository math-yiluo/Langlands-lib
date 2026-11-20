import Langlands.Geometry.FormalGroup.FieldRationalHeight
import Langlands.Geometry.FormalGroup.RationalEndAlgebra
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # The degree character of actual rational formal endomorphisms over a field -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.QuasiIsogeny

variable {O : Type u} [CommRing O] [IsDomain O] {π : O}
variable {k F : Type v} [Field k] [Field F] [Algebra O k] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O k σ} {N : ModuleLaw O k τ}

/-- A unit of the actual rational endomorphism ring supplies both inverse formal maps. -/
def ofEndUnit (a : (RationalHom F M M)ˣ) : QuasiIsogeny F M M where
  hom := a.val
  inv := a.inv
  inv_hom := a.inv_val
  hom_inv := a.val_inv

@[simp]
theorem ofEndUnit_hom (a : (RationalHom F M M)ˣ) : (ofEndUnit a).hom = a.val := rfl

@[simp]
theorem ofEndUnit_one : ofEndUnit (1 : (RationalHom F M M)ˣ) = refl M := rfl

theorem ofEndUnit_mul (a b : (RationalHom F M M)ˣ) :
    ofEndUnit (a * b) = (ofEndUnit b).trans (ofEndUnit a) :=
  ext rfl

variable [IsDiscreteValuationRing O]

/-- The rank ratio is one for an actual integral isomorphism. -/
@[simp]
theorem fieldDegree_ofIso (e : Iso M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    (ofIso (F := F) e).fieldDegree hπ hM hN = 1 := by
  rw [fieldDegree_ofHom _ hπ hM hN e.isIsogeny rfl,
    Hom.IsIsogeny.fieldDegree_eq_of_rank _ e.hasKernelRank_one, Nat.cast_one]

/-- The actual rank ratio defines a character on the rational endomorphism units. -/
def fieldDegreeUnits (hπ : Irreducible π) (hM : M.IsPiDivisible π) :
    (RationalHom F M M)ˣ →* ℚˣ where
  toFun a := Units.mk0 ((ofEndUnit a).fieldDegree hπ hM hM)
    ((ofEndUnit a).fieldDegree_pos hπ hM hM).ne'
  map_one' := Units.ext (by
    change (ofEndUnit (1 : (RationalHom F M M)ˣ)).fieldDegree hπ hM hM = 1
    rw [ofEndUnit_one, fieldDegree_refl])
  map_mul' a b := Units.ext (by
    change (ofEndUnit (a * b)).fieldDegree hπ hM hM =
      (ofEndUnit a).fieldDegree hπ hM hM * (ofEndUnit b).fieldDegree hπ hM hM
    rw [ofEndUnit_mul, fieldDegree_trans, mul_comm])

@[simp]
theorem fieldDegreeUnits_val (hπ : Irreducible π) (hM : M.IsPiDivisible π)
    (a : (RationalHom F M M)ˣ) :
    (fieldDegreeUnits hπ hM a : ℚ) = (ofEndUnit a).fieldDegree hπ hM hM := rfl

theorem fieldDegreeUnits_pos (hπ : Irreducible π) (hM : M.IsPiDivisible π)
    (a : (RationalHom F M M)ˣ) : 0 < (fieldDegreeUnits hπ hM a : ℚ) :=
  (ofEndUnit a).fieldDegree_pos hπ hM hM

variable {q H : ℕ}

/-- A cleared denominator gives a lower bound by the reciprocal of its actual scalar rank. -/
theorem inv_scalarRank_le_fieldDegreeUnits (hπ : Irreducible π) (hq : 0 < q)
    (hM : M.HasPiHeight π q H) (a : (RationalHom F M M)ˣ) {n : ℕ} {g : Hom M M}
    (hg : (algebraMap O F π) ^ n • a.val = RationalHom.ofHom g) :
    ((q : ℚ) ^ (n * H))⁻¹ ≤ (fieldDegreeUnits hπ hM.piDivisible a : ℚ) := by
  let e := ofEndUnit a
  let P : RationalHom.ScalarIsogenyPresentation π e.hom :=
    ⟨n, g, e.isIsogeny_of_clearsDenominator hπ hM.piDivisible hM.piDivisible hg, hg⟩
  rw [fieldDegreeUnits_val, e.fieldDegree_eq hπ hM.piDivisible hM.piDivisible P,
    P.degree_eq_div_scalarHeight hM, ← one_div]
  exact (div_le_div_iff_of_pos_right (pow_pos (by exact_mod_cast hq) _)).2
    (by exact_mod_cast P.isIsogeny.fieldDegree_pos)

/-- A common integral denominator for every signed power forces degree one. -/
theorem fieldDegreeUnits_eq_one_of_boundedPowers (hπ : Irreducible π) (hq : 0 < q)
    (hM : M.HasPiHeight π q H) (a : (RationalHom F M M)ˣ) (n : ℕ)
    (h : ∀ j : ℤ, ∃ g : Hom M M,
      (algebraMap O F π) ^ n • (a ^ j : (RationalHom F M M)ˣ).val = RationalHom.ofHom g) :
    fieldDegreeUnits hπ hM.piDivisible a = 1 := by
  let μ := fieldDegreeUnits (F := F) hπ hM.piDivisible
  let C : ℚ := ((q : ℚ) ^ (n * H))⁻¹
  have hC : 0 < C := inv_pos.mpr (pow_pos (by exact_mod_cast hq) _)
  have hb (j : ℤ) : C ≤ (μ (a ^ j) : ℚ) := by
    obtain ⟨g, hg⟩ := h j
    exact inv_scalarRank_le_fieldDegreeUnits hπ hq hM _ hg
  apply Units.ext
  change (μ a : ℚ) = 1
  apply le_antisymm
  · by_contra! hlt
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hC
      ((inv_lt_one₀ (lt_trans zero_lt_one hlt)).2 hlt)
    have hm' := hb (-(m : ℤ))
    rw [map_zpow, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast, ← inv_pow] at hm'
    exact (not_lt_of_ge hm') hm
  · by_contra! hlt
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hC hlt
    have hm' := hb (m : ℤ)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, zpow_natCast] at hm'
    exact (not_lt_of_ge hm') hm

/-- The scalar uniformizer has the degree of its actual finite kernel. -/
theorem fieldDegreeUnits_uniformizer (hπ : Irreducible π) (hM : M.HasPiHeight π q H)
    (t : Fˣ) (ht : (t : F) = algebraMap O F π) :
    (fieldDegreeUnits hπ hM.piDivisible
      (Units.map (algebraMap F (RationalHom F M M)).toMonoidHom t) : ℚ) = (q : ℚ) ^ H := by
  rw [fieldDegreeUnits_val]
  let e := ofEndUnit (Units.map (algebraMap F (RationalHom F M M)).toMonoidHom t)
  have he : e.hom = RationalHom.ofHom (M.scalarHom π) := by
    change algebraMap F (RationalHom F M M) (t : F) = _
    rw [RationalHom.algebraMap_eq_smul_id, ht, RationalHom.ofHom_scalarHom]
  exact (e.fieldDegree_ofHom hπ hM.piDivisible hM.piDivisible hM.scalar_height.1 he).trans (by
    rw [Hom.IsIsogeny.fieldDegree_eq_of_rank _ hM.scalar_height.2, Nat.cast_pow])

end Langlands.FormalGroup.ModuleLaw.QuasiIsogeny
