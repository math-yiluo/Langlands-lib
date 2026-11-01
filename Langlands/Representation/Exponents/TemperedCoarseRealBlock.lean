import Langlands.Representation.Exponents.InnerInducedCoarseScalar
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof

/-! The real central block of an actual tempered coarse twist. -/

noncomputable section

namespace Langlands.TemperedCoarseRealBlock

open GeneralLinear RelativeRegularComparison

universe uF uV

/-- The analytic unitary central character places the entire actual coarse
twist in its size-weighted real central block. -/
theorem realBlockEqTop
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (π : Rep.{uV} ℂ (B.Levi F.Carrier))
    (hπ : IsLeviTempered T B π) (t : Fin B.length → ℝ) :
    letI := T.topology
    T.realCentralBlock B (T.leviRealPowerTwist B t π.ρ)
      (fun k => (B.size k : ℝ) * t k) = ⊤ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  obtain ⟨c, _⟩ := (hπ μ).2
  let ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
    c.character.comp (B.blockScalarToCenter F.Carrier)
  let θ : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
    (T.leviRealPowerCharacter B t).comp (B.blockScalarLevi F.Carrier)
  let χ := ψ * θ
  have hscalar : Classification.HasScalarCharacter
      (T.leviRealPowerTwist B t π.ρ) (B.blockScalarLevi F.Carrier) χ := by
    intro a v
    change (T.leviRealPowerCharacter B t (B.blockScalarLevi F.Carrier a) : ℂ) •
      π.ρ (B.blockScalarLevi F.Carrier a) v = (χ a : ℂ) • v
    rw [show π.ρ (B.blockScalarLevi F.Carrier a) v =
      (c.character (B.blockScalarToCenter F.Carrier a) : ℂ) • v from
        c.acts (B.blockScalarToCenter F.Carrier a) v]
    simp only [χ, ψ, θ, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul,
      smul_smul]
    rw [mul_comm]
  apply InnerInducedCoarseScalar.realBlockEqTopOfScalar
    T B _ χ _ hscalar
    ((T.isSmooth_leviRealPowerTwist_iff B t π.ρ).mpr hπ.isAdmissible.1)
  intro a
  change ‖(ψ a : ℂ) * (θ a : ℂ)‖ = _
  rw [norm_mul,
    show ‖(ψ a : ℂ)‖ = 1 from c.norm_eq_one (B.blockScalarToCenter F.Carrier a),
    one_mul]
  change ‖(T.leviRealPowerCharacter B t (B.blockScalarLevi F.Carrier a) : ℂ)‖ = _
  rw [T.coe_leviRealPowerCharacter_blockScalar B, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun k _ =>
      Real.rpow_nonneg (T.normalizedAbs_nonneg _) _)]
end Langlands.TemperedCoarseRealBlock
