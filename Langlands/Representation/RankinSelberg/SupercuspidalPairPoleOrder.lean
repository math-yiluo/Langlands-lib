import Langlands.Representation.RankinSelberg.PoleOrderAtZeroArithmetic
import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.Twist.AlgebraProof
import Langlands.LocalField.Normalization.Proof

/-!
# Pole orders at `s = 0` from JPSS 1983, Proposition (8.1)

Assuming the statement `SupercuspidalEqualRankLFactorStatement` of JPSS 1983,
Proposition (8.1)(ii), the L-factor `L(s, π × σ)` of an irreducible
supercuspidal `π` and an irreducible `σ` of Whittaker type of the same rank has a
pole of order one at `s = 0` when `π ≅ σ̃`, and no pole there otherwise. This
order is recorded by the indicator `contragredientIndicator F π σ`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- The indicator of contragredience `[π ≅ σ̃]` of two representations of
`GL_(r+1)(F)`: `1` if `π` is equivalent to the smooth contragredient `σ̃` of `σ`,
and `0` otherwise. -/
def contragredientIndicator (F : PadicField.{uF} p) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W) : ℕ :=
  letI := F.canonicalTopologicalData.topology
  haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
  if Nonempty (π.Equiv (smoothContragredient σ)) then 1 else 0

/-- If `q^(-u) = 1`, then `|x|^(-u) = 1` for every nonzero `x` of `F`, since
`|x|` is an integral power of `q`. -/
theorem normalizedAbs_cpow_eq_one {F : PadicField.{uF} p} {u : ℂ}
    (hu : (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u) = 1)
    {x : F.Carrier} (hx : x ≠ 0) :
    ((F.canonicalTopologicalData.normalizedAbs x : ℝ) : ℂ) ^ (-u) = 1 := by
  rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero hx, Complex.ofReal_zpow,
    Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [Complex.natCast_arg, Real.pi_pos])
      (by simp [Complex.natCast_arg, Real.pi_pos.le]),
    Complex.cpow_int_mul, hu, one_zpow]

/-- The set `A` of JPSS 1983, Proposition (8.1)(ii), of the numbers `q^(-u)` with
`π ⊗ α^(-u) ≅ σ̃`, contains `1` exactly when `π ≅ σ̃`. -/
theorem one_mem_iff_of_supercuspidalTwistSet {F : PadicField.{uF} p} {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W}
    {A : Finset ℂ}
    (hA : ∀ a : ℂ, a ∈ A ↔ ∃ u : ℂ,
      a = (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u) ∧
      ∃ χ : F.Carrierˣ →* ℂˣ,
        (∀ x : F.Carrierˣ,
          (χ x : ℂ) = ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ (-u)) ∧
        letI := F.canonicalTopologicalData.topology
        haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
        Nonempty ((Langlands.twist (χ.comp determinant) π).Equiv (smoothContragredient σ))) :
    (1 : ℂ) ∈ A ↔
      letI := F.canonicalTopologicalData.topology
      haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
      Nonempty (π.Equiv (smoothContragredient σ)) := by
  rw [hA]
  constructor
  · rintro ⟨u, hu, χ, hχ, he⟩
    have hχ1 : χ = 1 := by
      ext x
      rw [hχ x, normalizedAbs_cpow_eq_one hu.symm x.ne_zero]
      simp
    subst hχ1
    simpa using he
  · intro he
    exact ⟨0, by simp, 1, fun x => by simp, by simpa using he⟩

/-- JPSS 1983, Proposition (8.1)(ii), at `s = 0`: for an irreducible supercuspidal
`π` and an irreducible `σ` of Whittaker type of `GL_(r+1)(F)`, the L-factor
`L(s, π × σ)` has a pole of order one at `s = 0` when `π ≅ σ̃` and no pole there
otherwise, that is, of order `contragredientIndicator F π σ`. The statement of
(8.1)(ii) is a hypothesis. -/
theorem lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank
    (h : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W]
    [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W}
    (hπ : Representation.IsIrreducible π)
    (hπs : letI := F.canonicalTopologicalData.topology; GeneralLinear.IsSupercuspidal π)
    (hσ : Representation.IsIrreducible σ)
    (hσw : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) σ)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν.val π σ P) :
    lPolynomialPoleOrderAtZero P = contragredientIndicator F π σ := by
  classical
  obtain ⟨A, hA, hPA⟩ := h p F ψ ν r π σ hπ hπs hσ hσw
  rw [hP.unique hPA, lPolynomialPoleOrderAtZero_prod_one_sub_C_mul_X, contragredientIndicator]
  exact if_congr (one_mem_iff_of_supercuspidalTwistSet hA) rfl rfl

end Langlands.RankinSelberg
