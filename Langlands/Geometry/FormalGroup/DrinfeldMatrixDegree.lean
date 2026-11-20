import Langlands.Geometry.FormalGroup.DrinfeldDivisionDegree
import Langlands.Geometry.FormalGroup.DrinfeldMatrixFrame
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-! # The degree of the actual matrix action on a formal frame -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u s w

namespace Langlands.FormalGroup.LocalDivision.SpecialModule.MatrixCoordinates

open ValuativeRel CentralSimple ModuleLaw
open scoped NNReal

private theorem positiveCharacter_pow_card
    {n : Type w} {K : Type u} [Fintype n] [DecidableEq n] [Field K]
    (χ : GL n K →* ℚˣ) (hpos : ∀ g, 0 < (χ g : ℚ)) (g : GL n K) :
    (χ g : ℚ) ^ Fintype.card n = (χ (Matrix.GeneralLinearGroup.scalar n (g.det)) : ℚ) := by
  let scalarDet := (Matrix.GeneralLinearGroup.scalar n).comp
    (Matrix.GeneralLinearGroup.det : GL n K →* Kˣ)
  let ratio := ((powMonoidHom (Fintype.card n)).comp χ) / (χ.comp scalarDet)
  let norm : ℚˣ →* ℝ≥0 := (nnnormHom.toMonoidHom : ℝ →* ℝ≥0).comp
    ((Rat.castHom ℝ).toMonoidHom.comp (Units.coeHom ℚ))
  have hscalar (a : Kˣ) : (norm.comp ratio) (Matrix.GeneralLinearGroup.scalar n a) = 1 := by
    have hr : ratio (Matrix.GeneralLinearGroup.scalar n a) = 1 := by
      change χ (Matrix.GeneralLinearGroup.scalar n a) ^ Fintype.card n /
        χ (Matrix.GeneralLinearGroup.scalar n ((Matrix.GeneralLinearGroup.scalar n a).det)) = 1
      rw [Matrix.GeneralLinearGroup.det_scalar, map_pow, map_pow, div_self']
    change norm (ratio (Matrix.GeneralLinearGroup.scalar n a)) = 1
    rw [hr, map_one]
  have h := Langlands.RankinSelberg.GeneralLinearUnimodularity.character_eq_one
    (norm.comp ratio) hscalar g
  have hval := congrArg (fun a : ℝ≥0 => (a : ℝ)) h
  change |(((ratio g : ℚ) : ℝ))| = 1 at hval
  have hrpos : 0 < (ratio g : ℚ) := by
    change 0 < ((χ g ^ Fintype.card n / χ (scalarDet g) : ℚˣ) : ℚ)
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    exact div_pos (pow_pos (hpos g) _) (hpos _)
  rw [abs_of_pos (by exact_mod_cast hrpos)] at hval
  have hr : (ratio g : ℚ) = 1 := by exact_mod_cast hval
  change ((χ g ^ Fintype.card n / χ (scalarDet g) : ℚˣ) : ℚ) = 1 at hr
  rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_one_iff_eq (Units.ne_zero _)] at hr
  exact hr

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ]
variable {Φ : SpecialModule K D ι κ} (c : Φ.MatrixCoordinates) {π : 𝒪[K]}

/-- The degree character of the actual matrix quasi-isogenies in the chosen frame coordinates. -/
def degree (hπ : Irreducible π) (hΦ : Φ.formalModule.IsPiDivisible π) :
    GL (Fin (reducedDegree K D)) K →* ℚˣ :=
  (QuasiIsogeny.fieldDegreeUnits hπ hΦ).comp
    (Units.map
      { toFun := fun g => (c g).val
        map_one' := congrArg Subtype.val c.map_one
        map_mul' := fun g h => congrArg Subtype.val (c.map_mul g h) })

theorem degree_val (hπ : Irreducible π) (hΦ : Φ.formalModule.IsPiDivisible π)
    (g : GL (Fin (reducedDegree K D)) K) :
    (c.degree hπ hΦ g : ℚ) =
      (c.quasiIsogeny g).toModuleQuasiIsogeny.fieldDegree hπ hΦ hΦ := rfl

theorem degree_pos (hπ : Irreducible π) (hΦ : Φ.formalModule.IsPiDivisible π)
    (g : GL (Fin (reducedDegree K D)) K) :
    0 < (c.degree hπ hΦ g : ℚ) := QuasiIsogeny.fieldDegreeUnits_pos hπ hΦ _

/-- Matrix and division coordinates induce the same degree on actual central scalars. -/
theorem degree_scalar (hπ : Irreducible π) (hΦ : Φ.formalModule.IsPiDivisible π) (a : Kˣ) :
    c.degree hπ hΦ (Matrix.GeneralLinearGroup.scalar (Fin (reducedDegree K D)) a) =
      DrinfeldAction.divisionDegree Φ.order hπ hΦ (Units.map (algebraMap K D).toMonoidHom a) := by
  apply congrArg (QuasiIsogeny.fieldDegreeUnits hπ hΦ)
  apply Units.ext
  change (c (Matrix.scalar _ (a : K))).val = rationalAction K D Φ.order (algebraMap K D (a : K))
  rw [(rationalAction K D Φ.order).commutes]
  exact congrArg Subtype.val (c.commutes (a : K))

set_option maxHeartbeats 1000000 in
/-- A scalar height `H*d` gives matrix degree `q^(H*ord(det g))`. -/
theorem degree_eq_zpow {q H : ℕ} (hq : 0 < q) (hπ : Irreducible π)
    (hΦ : Φ.formalModule.HasPiHeight π q (H * reducedDegree K D))
    (g : GL (Fin (reducedDegree K D)) K) :
    (c.degree hπ hΦ.piDivisible g : ℚ) =
      (q : ℚ) ^ ((H : ℤ) * (Plancherel.fieldOrderUnits K g.det).toAdd) := by
  let μ := c.degree hπ hΦ.piDivisible
  let d := reducedDegree K D
  let r := (Plancherel.fieldOrderUnits K g.det).toAdd
  have hpow : (μ g : ℚ) ^ d = (μ (Matrix.GeneralLinearGroup.scalar (Fin d) g.det) : ℚ) := by
    simpa only [Fintype.card_fin] using positiveCharacter_pow_card μ
      (c.degree_pos hπ hΦ.piDivisible) g
  have hs : (μ (Matrix.GeneralLinearGroup.scalar (Fin d) g.det) : ℚ) =
      (q : ℚ) ^ ((H : ℤ) * ((d : ℤ) * r)) := by
    change (c.degree hπ hΦ.piDivisible (Matrix.GeneralLinearGroup.scalar (Fin d) g.det) : ℚ) = _
    rw [c.degree_scalar hπ hΦ.piDivisible, DrinfeldAction.divisionDegree_eq_zpow hq _ hπ hΦ,
      DrinfeldAction.divisionUnitOrder_scalar]
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  change (μ g : ℚ) = (q : ℚ) ^ ((H : ℤ) * r)
  apply (pow_left_inj₀ (c.degree_pos hπ hΦ.piDivisible g).le
    (zpow_pos hq' _).le (reducedDegree_pos K D).ne').mp
  refine hpow.trans (hs.trans ?_)
  rw [← zpow_natCast ((q : ℚ) ^ ((H : ℤ) * r)) d, ← zpow_mul]
  congr 1
  ring

end Langlands.FormalGroup.LocalDivision.SpecialModule.MatrixCoordinates
