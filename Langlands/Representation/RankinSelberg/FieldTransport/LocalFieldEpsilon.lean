import Langlands.Representation.RankinSelberg.FieldTransport.Padic
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
import Langlands.LocalField.ContinuousIntegerTransport

/-! # Normalized JPSS epsilon factors under bicontinuous local-field isomorphisms -/

noncomputable section

set_option autoImplicit false

universe u v uV uW

namespace Langlands.LocalFieldData

variable {F : Type u} {E : Type v} [Field F] [Field E]
  (TF : LocalFieldData F) (TE : LocalFieldData E) (σ : F ≃+* E)
  (hσ : @Continuous F E TF.topology TE.topology σ)
  (hσs : @Continuous E F TE.topology TF.topology σ.symm)

/-- Restrict the supplied field equivalence to the actual valuation rings. -/
def integerRingEquivOfContinuous : TF.Integers ≃+* TE.Integers where
  toFun x := ⟨σ x, (TF.mem_integers_iff_of_continuous_ringEquiv TE σ hσ hσs x).mp x.2⟩
  invFun y := ⟨σ.symm y,
    (TE.mem_integers_iff_of_continuous_ringEquiv TF σ.symm hσs hσ y).mp y.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add σ (x : F) (y : F))

include σ hσ hσs in
/-- A bicontinuous field equivalence preserves the actual residue cardinality. -/
theorem residueCardinality_of_continuous_ringEquiv :
    TE.residueCardinality = TF.residueCardinality :=
  (Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv (TF.integerRingEquivOfContinuous TE σ hσ hσs)).toEquiv).symm

private theorem mem_integers_iff_ord_nonneg {x : F} (hx : x ≠ 0) :
    x ∈ TF.Integers ↔ 0 ≤ TF.ord x := by
  rw [← TF.normalizedAbs_le_one_iff_mem_integers, TF.normalizedAbs_of_ne_zero hx]
  have hq : (1 : ℝ) < TF.residueCardinality := by exact_mod_cast TF.residueCardinality_gt_one
  rw [← zpow_zero (TF.residueCardinality : ℝ), zpow_le_zpow_iff_right₀ hq,
    neg_nonpos]

private theorem ord_le_iff_mem_div {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    TF.ord x ≤ TF.ord y ↔ y / x ∈ TF.Integers := by
  rw [mem_integers_iff_ord_nonneg TF (div_ne_zero hy hx), div_eq_mul_inv,
    TF.ord_mul hy (inv_ne_zero hx), TF.ord_inv]
  omega

include hσ hσs in
/-- Comparing the orders of nonzero elements amounts to testing integrality
of their ratio, which can be done on either side of the equivalence. -/
theorem ord_le_of_continuous_ringEquiv {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    TE.ord (σ x) ≤ TE.ord (σ y) ↔ TF.ord x ≤ TF.ord y := by
  rw [ord_le_iff_mem_div TE ((map_ne_zero σ).mpr hx) ((map_ne_zero σ).mpr hy),
    ord_le_iff_mem_div TF hx hy, ← map_div₀ σ,
    ← TF.mem_integers_iff_of_continuous_ringEquiv TE σ hσ hσs]

private theorem local_uniformizer_ne_zero : TF.uniformizer ≠ 0 := by
  intro h
  have ho := TF.ord_uniformizer
  rw [h, TF.ord_zero] at ho
  exact zero_ne_one ho

include hσ hσs in
/-- The least positive order is one in each field, hence the image of a
uniformizer has order one. Comparison with its powers gives equality of orders. -/
theorem ord_of_continuous_ringEquiv (x : F) : TE.ord (σ x) = TF.ord x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, TF.ord_zero, TE.ord_zero]
  have hrel {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :=
    TF.ord_le_of_continuous_ringEquiv TE σ hσ hσs hx hy
  have hpos {y : F} (hy : y ≠ 0) : 0 < TE.ord (σ y) ↔ 0 < TF.ord y := by
    simpa only [map_one, TF.ord_one, TE.ord_one, not_le] using (hrel hy one_ne_zero).not
  have hF := local_uniformizer_ne_zero TF
  have hE := local_uniformizer_ne_zero TE
  have hl := (hpos hF).mpr (TF.ord_uniformizer.symm ▸ Int.zero_lt_one)
  have hp := (hpos ((map_ne_zero σ.symm).mpr hE)).mp (by
    rw [σ.apply_symm_apply, TE.ord_uniformizer]
    exact Int.zero_lt_one)
  have hu := (hrel hF ((map_ne_zero σ.symm).mpr hE)).mpr (by
    rw [TF.ord_uniformizer]
    omega)
  rw [σ.apply_symm_apply, TE.ord_uniformizer] at hu
  have hπ : TE.ord (σ TF.uniformizer) = 1 := by omega
  let y := TF.uniformizer ^ TF.ord x
  have hy : y ≠ 0 := zpow_ne_zero _ hF
  have hFy : TF.ord y = TF.ord x := by
    dsimp only [y]
    rw [TF.ord_zpow, TF.ord_uniformizer, mul_one]
  have hEy : TE.ord (σ y) = TF.ord x := by
    dsimp only [y]
    rw [map_zpow₀, TE.ord_zpow, hπ, mul_one]
  rw [← hEy]
  exact le_antisymm ((hrel hx hy).mpr hFy.ge) ((hrel hy hx).mpr hFy.le)

include hσ hσs in
/-- The normalized absolute values correspond, with no residual power. -/
theorem normalizedAbs_of_continuous_ringEquiv (x : F) :
    TE.normalizedAbs (σ x) = TF.normalizedAbs x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, TF.normalizedAbs_zero, TE.normalizedAbs_zero]
  rw [TE.normalizedAbs_of_ne_zero ((map_ne_zero σ).mpr hx), TF.normalizedAbs_of_ne_zero hx,
    TF.residueCardinality_of_continuous_ringEquiv TE σ hσ hσs,
    TF.ord_of_continuous_ringEquiv TE σ hσ hσs]

end Langlands.LocalFieldData

namespace Langlands.RankinSelberg.FieldTransport

open MeasureTheory Langlands.HarmonicAnalysis Langlands.Whittaker Langlands.GeneralLinear

variable {F : Type u} {E : Type v} [Field F] [Field E] [TopologicalSpace F]
  [TopologicalSpace E] [ValuativeRel F] [ValuativeRel E]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  {ν : letI := borel F; AdditiveHaarMeasure F}
  {ν' : letI := borel E; AdditiveHaarMeasure E}
  (hψ : ∀ x, ψ' (σ x) = ψ x)
  (hν : letI := borel F; letI := borel E; ν'.measure = ν.measure.map σ)
  {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
  (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) (a : ℂˣ × ℤ)

include hψ hν in
/-- The coefficient and exponent of the normalized actual JPSS epsilon factor
transport without change under a bicontinuous field equivalence. -/
theorem isLocalPairEpsilonFactor_comp_iff :
    AllField.RankinSelberg.IsPadicPairEpsilonFactor E ψ' ν' π τ a ↔
    AllField.RankinSelberg.IsPadicPairEpsilonFactor F ψ ν
      (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
      (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) a := by
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel E
  let : BorelSpace E := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) E)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) E) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) E)
  let : BorelSpace (upperUnipotent (n + 1) E) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n E)
  let : BorelSpace (LeftUnipotentQuotient n E) := ⟨rfl⟩
  let : SigmaCompactSpace E := TE.sigmaCompactSpace
  let : IsFiniteMeasureOnCompacts ν'.measure := ν'.isAddHaar.toIsFiniteMeasureOnCompacts
  let : SigmaFinite ν'.measure := SigmaFinite.of_isFiniteMeasureOnCompacts ν'.measure
  have hO (x : F) : σ x ∈ (ValuativeRel.valuation E).integer ↔
      x ∈ (ValuativeRel.valuation F).integer :=
    (TF.mem_integers_iff_of_continuous_ringEquiv TE σ hσ hσs x).symm
  have hU := (unipotentHaar_map (F := F) (E := E) σ hσ hσs hO n).symm
  have hG := (generalLinearHaar_map (F := F) (E := E) σ hσ hσs hO n).symm
  have habv (x : F) : AllField.RankinSelberg.normalizedAbsoluteValue TE (σ x) =
      AllField.RankinSelberg.normalizedAbsoluteValue TF x :=
    TF.normalizedAbs_of_continuous_ringEquiv TE σ hσ hσs x
  unfold AllField.RankinSelberg.IsPadicPairEpsilonFactor
  rw [show (⟨⟩ : LocalFieldData E).residueCardinality = (⟨⟩ : LocalFieldData F).residueCardinality
    from TF.residueCardinality_of_continuous_ringEquiv TE σ hσ hσs]
  exact isPairEpsilonFactor_comp_iff σ hσ hσs hψ habv _ ν ν' hν hG hU π τ a

include hψ hν in
/-- The symmetric epsilon relation uses the same rank order on both fields. -/
theorem isLocalSymmetricEpsilonFactor_comp_iff :
    AllField.RankinSelberg.IsPadicSymmetricEpsilonFactor E ψ' ν' π τ a ↔
    AllField.RankinSelberg.IsPadicSymmetricEpsilonFactor F ψ ν
      (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
      (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) a := by
  unfold AllField.RankinSelberg.IsPadicSymmetricEpsilonFactor
  split_ifs
  · exact isLocalPairEpsilonFactor_comp_iff σ hσ hσs hψ hν π τ a
  · exact isLocalPairEpsilonFactor_comp_iff σ hσ hσs hψ hν τ π a

/-- A bicontinuous isomorphism of actual local fields preserves the residue
cardinality and transports the symmetric JPSS epsilon certificate. -/
def LocalFieldEpsilonTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] (E : Type v) [Field E] [TopologicalSpace E]
    [ValuativeRel E] [IsNonarchimedeanLocalField E]
    (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm),
    (LocalFieldData.ofInstances E).residueCardinality =
        (LocalFieldData.ofInstances F).residueCardinality ∧
    ∀ (ψ : UnitaryAdditiveCharacter F) (ψ' : UnitaryAdditiveCharacter E)
      (ν : letI := borel F; AdditiveHaarMeasure F)
      (ν' : letI := borel E; AdditiveHaarMeasure E),
      (∀ x, ψ' (σ x) = ψ x) →
      (letI := borel F; letI := borel E; ν'.measure = ν.measure.map σ) →
    ∀ (r n : ℕ) (V : Type uV) (W : Type uW) [AddCommGroup V] [Module ℂ V]
      [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) (a : ℂˣ × ℤ),
      AllField.RankinSelberg.IsPadicSymmetricEpsilonFactor E ψ' ν' π τ a ↔
      AllField.RankinSelberg.IsPadicSymmetricEpsilonFactor F ψ ν
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) a

theorem localFieldEpsilonTransport : LocalFieldEpsilonTransportStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ E _ _ _ _ σ hσ hσs
  refine ⟨(LocalFieldData.ofInstances F).residueCardinality_of_continuous_ringEquiv
    (LocalFieldData.ofInstances E) σ hσ hσs, ?_⟩
  intro ψ ψ' ν ν' hψ hν r n V W _ _ _ _ π τ a
  exact isLocalSymmetricEpsilonFactor_comp_iff σ hσ hσs hψ hν π τ a

end Langlands.RankinSelberg.FieldTransport
