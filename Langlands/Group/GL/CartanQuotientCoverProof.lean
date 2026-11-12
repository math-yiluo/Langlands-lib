import Langlands.Group.GL.CartanQuotientCoverStatement
import Langlands.Group.GL.CartanQuotientLawsProof
import Langlands.Group.GL.CartanProof
import Langlands.LocalField.Normalization.Proof

/-! # Normalized Cartan covering modulo the entire center -/

noncomputable section

namespace Langlands.GeneralLinear.CartanQuotient

open LocalFactor.PadicAbelian
open scoped WithZero

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The specified unit uniformizes the discrete valuation for every supplied
topological datum. -/
theorem uniformizer_isUniformizingElement :
    Iwasawa.IsUniformizingElement T.discreteValuation (uniformizerUnit T) := by
  constructor
  · rw [uniformizerUnit_coe, T.discreteValuation_uniformizer]
    norm_num
  · intro x hx
    refine ⟨-WithZero.log (T.discreteValuation x), ?_⟩
    rw [uniformizerUnit_coe, T.discreteValuation_uniformizer, ← WithZero.exp_zsmul]
    simpa [zsmul_eq_mul] using
      (WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr hx)).symm

/-- Every scalar unit is a uniformizer power times a valuation-one unit. -/
theorem scalar_unit_split (u : F.Carrierˣ) :
    ∃ (e : ℤ) (ε : F.Carrierˣ), T.discreteValuation (ε : F.Carrier) = 1 ∧
      u = uniformizerUnit T ^ e * ε := by
  obtain ⟨e, he⟩ := (uniformizer_isUniformizingElement T).2 (u : F.Carrier) u.ne_zero
  let ε := u * (uniformizerUnit T ^ e)⁻¹
  refine ⟨e, ε, ?_, ?_⟩
  · rw [show (ε : F.Carrier) = (u : F.Carrier) *
        (((uniformizerUnit T ^ e)⁻¹ : F.Carrierˣ) : F.Carrier) from rfl,
      map_mul, he, Units.val_inv_eq_inv_val, map_inv₀,
      Units.val_zpow_eq_zpow_val, map_zpow₀, mul_inv_cancel₀]
    exact zpow_ne_zero _ (T.discreteValuation.ne_zero_iff.mpr (uniformizerUnit T).ne_zero)
  · simp [ε, mul_left_comm]

/-- Valuation-one scalar matrices belong to the actual integral subgroup. -/
theorem scalar_mem_maximalCompact {n : ℕ} (u : F.Carrierˣ)
    (hu : T.discreteValuation (u : F.Carrier) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin n) u ∈ maximalCompact T n := by
  cases n with
  | zero =>
      have h : Matrix.GeneralLinearGroup.scalar (Fin 0) u = 1 := Subsingleton.elim _ _
      rw [h]
      exact one_mem _
  | succ n =>
      have h : Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) u =
          Iwasawa.diagonalUnits (fun _ : Fin (n + 1) => u) := by
        apply Units.ext
        rfl
      rw [h]
      exact Iwasawa.diagonalUnits_mem T.discreteValuation _ (fun _ => hu)

/-- Equality in the actual central quotient lifts to multiplication by a scalar
unit of the field. -/
theorem quotientMap_eq_iff_scalar {n : ℕ} (g h : GeneralLinear n F.Carrier) :
    quotientMap F n g = quotientMap F n h ↔
      ∃ u : F.Carrierˣ, g * Matrix.GeneralLinearGroup.scalar (Fin n) u = h := by
  rw [QuotientGroup.mk'_eq_mk', Matrix.GeneralLinearGroup.center_eq_range_scalar]
  simp

/-- A scalar discrepancy in the quotient is a uniformizer scalar followed by
an actual integral scalar factor. -/
theorem quotientMap_eq_power_integral {n : ℕ} {g h : GeneralLinear n F.Carrier}
    (hgh : quotientMap F n g = quotientMap F n h) :
    ∃ (e : ℤ) (k : GeneralLinear n F.Carrier), k ∈ maximalCompact T n ∧
      Matrix.GeneralLinearGroup.scalar (Fin n) (uniformizerUnit T ^ e) * g * k = h := by
  obtain ⟨u, hu⟩ := (quotientMap_eq_iff_scalar g h).1 hgh
  obtain ⟨e, ε, hε, huε⟩ := scalar_unit_split T u
  refine ⟨e, Matrix.GeneralLinearGroup.scalar (Fin n) ε,
    scalar_mem_maximalCompact T ε hε, ?_⟩
  calc
    _ = g * Matrix.GeneralLinearGroup.scalar (Fin n) (uniformizerUnit T ^ e) *
        Matrix.GeneralLinearGroup.scalar (Fin n) ε := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
    _ = g * Matrix.GeneralLinearGroup.scalar (Fin n) u := by
      rw [mul_assoc, ← map_mul, ← huε]
    _ = h := hu

/-- Quotient equality between two integral factorizations lifts to a GL
factorization with one uniformizer scalar and integral outer factors. -/
theorem integral_factors_eq_of_quotient_eq {n : ℕ} {lam mu : Fin n → ℤ}
    {k₁ k₂ l₁ l₂ : GeneralLinear n F.Carrier}
    (hk₂ : k₂ ∈ maximalCompact T n)
    (h : quotientMap F n (k₁ * representative T lam * k₂) =
      quotientMap F n (l₁ * representative T mu * l₂)) :
    ∃ (e : ℤ) (k₃ : GeneralLinear n F.Carrier), k₃ ∈ maximalCompact T n ∧
      k₁ * (Matrix.GeneralLinearGroup.scalar (Fin n) (uniformizerUnit T ^ e) *
        representative T lam) * k₃ = l₁ * representative T mu * l₂ := by
  obtain ⟨e, k, hk, he⟩ := quotientMap_eq_power_integral T h
  refine ⟨e, k₂ * k, (maximalCompact T n).mul_mem hk₂ hk, ?_⟩
  calc
    _ = (k₁ * Matrix.GeneralLinearGroup.scalar (Fin n) (uniformizerUnit T ^ e)) *
        (representative T lam * (k₂ * k)) := by simp only [mul_assoc]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin n) (uniformizerUnit T ^ e) * k₁) *
        (representative T lam * (k₂ * k)) := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
    _ = Matrix.GeneralLinearGroup.scalar (Fin n) (uniformizerUnit T ^ e) *
        (k₁ * representative T lam * k₂) * k := by simp only [mul_assoc]
    _ = _ := he

/-- A common shift between two normalized tuples vanishes. -/
theorem eq_of_normalized_shift {n : ℕ} {lam mu : Fin n → ℤ} {c : ℤ}
    (hlam : Normalized lam) (hmu : Normalized mu) (h : shift lam c = mu) :
    lam = mu := by
  obtain ⟨i, hi⟩ := hlam.2.2
  obtain ⟨j, hj⟩ := hmu.2.2
  have hei : lam i + c = mu i := congrFun h i
  have hej : lam j + c = mu j := congrFun h j
  have hli := hlam.2.1 j
  have hmj := hmu.2.1 i
  have hc : c = 0 := by omega
  funext a
  have hea : lam a + c = mu a := congrFun h a
  omega

/-- Two normalized cells containing the same point have the same exponent tuple. -/
theorem normalized_eq_of_mem {n : ℕ} {lam mu : Fin n → ℤ}
    (hlam : Normalized lam) (hmu : Normalized mu) {x : centralQuotient F n}
    (hxlam : x ∈ cell T lam) (hxmu : x ∈ cell T mu) :
    lam = mu := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hxlam⟩ := hxlam
  obtain ⟨l₁, hl₁, l₂, hl₂, hxmu⟩ := hxmu
  obtain ⟨e, k₃, hk₃, he⟩ :=
    integral_factors_eq_of_quotient_eq T hk₂ (hxlam.symm.trans hxmu)
  rw [← representative_shift T lam e] at he
  have hanti : Antitone (shift lam e) := by
    intro i j hij
    have := hlam.1 hij
    change lam j + e ≤ lam i + e
    omega
  have hshift : shift lam e = mu :=
    Cartan.exponent_unique (uniformizer_isUniformizingElement T)
      hanti hmu.1 hk₁ hk₃ hl₁ hl₂ he
  exact eq_of_normalized_shift hlam hmu hshift

/-- Every actual central quotient point has a unique normalized Cartan tuple. -/
theorem cartanQuotientCover : CartanQuotientCoverStatement.{uF} := by
  intro p _ F T n hn x
  cases n with
  | zero => omega
  | succ m =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center (GeneralLinear (m + 1) F.Carrier)) x
      obtain ⟨a, ⟨ha, k₁, hk₁, k₂, hk₂, hg⟩, _⟩ :=
        Cartan.cartanDecomposition F.Carrier ℤᵐ⁰ T.discreteValuation
          (uniformizerUnit T) (uniformizer_isUniformizingElement T) (m + 1) g
      let lam := shift a (-a (Fin.last m))
      have hlam : Normalized lam := by
        apply (normalized_iff_antitone_last_eq_zero m lam).2
        refine ⟨?_, ?_⟩
        · intro i j hij
          have := ha hij
          change a j + -a (Fin.last m) ≤ a i + -a (Fin.last m)
          omega
        · simp [lam, shift]
      have hx : quotientMap F (m + 1) g ∈ cell T lam := by
        rw [show lam = shift a (-a (Fin.last m)) from rfl, cell_shift]
        exact ⟨k₁, hk₁, k₂, hk₂, congrArg (quotientMap F (m + 1)) hg⟩
      refine ⟨lam, ⟨hlam, hx⟩, ?_⟩
      intro mu hmu
      exact normalized_eq_of_mem T hmu.1 hlam hmu.2 hx

/-- Distinct normalized Cartan tuples give disjoint subsets of the actual quotient. -/
theorem cartanQuotientDisjoint : CartanQuotientDisjointStatement.{uF} := by
  intro p _ F T n hn lam mu hlam hmu hne
  apply Set.disjoint_left.mpr
  intro x hxlam hxmu
  obtain ⟨a, _, huniq⟩ := cartanQuotientCover p F T n hn x
  exact hne ((huniq lam ⟨hlam, hxlam⟩).trans (huniq mu ⟨hmu, hxmu⟩).symm)

end Langlands.GeneralLinear.CartanQuotient
