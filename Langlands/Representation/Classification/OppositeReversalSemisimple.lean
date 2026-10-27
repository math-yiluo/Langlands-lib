import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.Classification.TemperedInductionStatement
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-!
# Opposite induction of an arbitrary Levi representation by block reversal

Conjugation by the block-reversal matrix identifies opposite normalized
induction from `B` with upper normalized induction from `B.reverse` of the
pullback along the block-reindexing isomorphism of the Levi groups. The
semisimplicity consequence is stated conditionally on the tempered induction
proposition; no analytic assertion is proved here.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The reversed Levi product is the original Levi product with reversed
block labels: `m ↦ (i ↦ m i.rev)`, inverted. -/
def leviReverse :
    letI := T.topology
    B.reverse.Levi F.Carrier ≃ₜ* B.Levi F.Carrier :=
  letI := T.topology
  (FiniteTensor.reindexGroupContinuous
    (fun i => GeneralLinear (B.size i) F.Carrier) Fin.revPerm).symm

/-- The opposite block projection of a conjugated reversed-parabolic element is
the reindexed upper block projection. -/
theorem oppositeLeviProjection_reverseToOpposite_eq
    (q : B.reverse.parabolic F.Carrier) :
    letI := T.topology
    B.oppositeLeviProjection F.Carrier (B.reverseToOpposite F.Carrier q) =
      T.leviReverse B (B.reverse.leviProjection F.Carrier q) := by
  let := T.topology
  apply (FiniteTensor.reindexGroup
    (fun i => GeneralLinear (B.size i) F.Carrier) Fin.revPerm).injective
  erw [MulEquiv.apply_symm_apply]
  funext i
  exact B.oppositeLeviProjection_reverseToOpposite F.Carrier q i

/-- Opposite normalized induction from `B` of an arbitrary Levi
representation `σ` is equivalent to upper normalized induction from
`B.reverse` of `σ` pulled back along `leviReverse`. -/
def oppositeReversalEquiv (σ : Representation ℂ (B.Levi F.Carrier) W) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedOppositeParabolicInduced B σ).Equiv
      (T.normalizedParabolicInduced B.reverse
        (σ.comp (T.leviReverse B).toMonoidHom)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let w := B.reverseMatrix F.Carrier
  let e := B.reverseToOpposite F.Carrier
  let ρ := twist (T.oppositeParabolicHalfModulus B)
    (σ.comp (B.oppositeLeviProjection F.Carrier))
  let α : Representation ℂ (B.reverse.parabolic F.Carrier) W := ρ.comp e.toMonoidHom
  let τ := twist (T.parabolicHalfModulus B.reverse)
    ((σ.comp (T.leviReverse B).toMonoidHom).comp (B.reverse.leviProjection F.Carrier))
  let D : α.Equiv τ := Representation.Equiv.mk (LinearEquiv.refl ℂ W) (fun q => by
    apply LinearMap.ext
    intro v
    change (T.oppositeParabolicHalfModulus B (e q) : ℂ) •
        σ (B.oppositeLeviProjection F.Carrier (e q)) v =
      (T.parabolicHalfModulus B.reverse q : ℂ) •
        σ (T.leviReverse B (B.reverse.leviProjection F.Carrier q)) v
    rw [T.oppositeHalfModulus_reverseToOpposite B q,
      T.oppositeLeviProjection_reverseToOpposite_eq B q])
  let C : (Induction.smoothInduced _ α).Equiv (Induction.smoothInduced _ ρ) :=
    Induction.conjugateSmoothInducedEquiv w e (fun _ => rfl) (fun _ => rfl)
  C.symm.trans (Induction.smoothInducedEquiv _ D)

end Langlands.PadicField.TopologicalData

namespace Langlands

universe uF uW

/-- Conditional on tempered upper induction at universe `uW`, opposite
normalized induction of an irreducible representation of the actual product
Levi that is tempered modulo the center for a Haar measure is semisimple. -/
theorem isSemisimple_normalizedOppositeParabolicInduced_of_temperedInduction
    (h1 : GLTemperedInductionStatement.{uF, uW})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    let M := B.Levi F.Carrier
    let Q := M ⧸ Subgroup.center M
    ∀ [MeasurableSpace Q] [BorelSpace Q]
      (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
      {W : Type uW} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ M W),
      Representation.IsIrreducible σ → IsTemperedModCenter σ μ →
        Representation.IsSemisimpleRepresentation
          (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro M Q _ _ μ _ W _ _ σ hσ hσt
  let := T.leviTopologicalGroup B.reverse
  let := T.generalLinearTopologicalGroup n
  let φ := T.leviReverse B
  let M' := B.reverse.Levi F.Carrier
  let Q' := M' ⧸ Subgroup.center M'
  let : MeasurableSpace Q' := borel Q'
  have : BorelSpace Q' := ⟨rfl⟩
  let ψ := centralQuotientCongr φ
  let μ' : MeasureTheory.Measure Q' := μ.map ψ.symm
  have : μ'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ ψ.symm
  have hμ : μ'.map ψ = μ := by
    change (μ.map ψ.symm).map ψ = μ
    have hψ : Measurable (ψ : Q' → Q) := ψ.continuous.measurable
    have hψs : Measurable (ψ.symm : Q → Q') := ψ.symm.continuous.measurable
    rw [MeasureTheory.Measure.map_map hψ hψs]
    have hid : (ψ : Q' → Q) ∘ ψ.symm = id := by
      funext x
      exact ψ.apply_symm_apply x
    rw [hid, MeasureTheory.Measure.map_id]
  have htemp : ∀ (ν : MeasureTheory.Measure Q) [ν.IsHaarMeasure], ν = μ →
      IsTemperedModCenter σ ν := by
    intro ν _ hν
    subst hν
    exact hσt
  have hσ't : IsTemperedModCenter (σ.comp φ.toMonoidHom) μ' :=
    isTemperedModCenter_comp_continuousMulEquiv σ φ μ' (htemp _ hμ)
  have hσ' : Representation.IsIrreducible (σ.comp φ.toMonoidHom) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff σ φ.toMulEquiv).mpr hσ
  have hss := (h1 p F T n hn B.reverse μ' W (σ.comp φ.toMonoidHom) hσ' hσ't).2.1
  let E := T.oppositeReversalEquiv B σ
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hss ⊢
  exact ((Representation.IntertwiningMap.equivLinearMapAsModule _ _
    E.symm.toIntertwiningMap).isSemisimpleModule_iff_of_bijective E.symm.bijective).mp hss

end Langlands
