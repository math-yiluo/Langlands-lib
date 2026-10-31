import Langlands.Representation.Classification.RegularLanglandsHeadAdapters
import Langlands.Representation.Classification.TemperedJointSupportProof
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Tensor.FiniteProperties

/-! The supported all-regular comparison implies regular tempered GL heads. -/

noncomputable section

namespace Langlands

universe uF uV

namespace RegularHeadExistence

/-- The actual smooth canonical head, certified using joint support and the
supported all-regular relative comparison. -/
def canonicalHeadOfRelativeRegularComparison
    (hcomp : GLRelativeRegularComparisonStatement.{uF, max uF uV, max uF uV,
      max uF uV})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (d : T.TemperedLanglandsDatum.{max uF uV, uF} n) :
    letI := T.topology
    {π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) //
      d.IsLanglandsHead π} := by
  let := T.topology
  refine ⟨d.standardModule.headQuotient, ?_⟩
  let π : Rep.{max uF uV} ℂ (d.shape.Levi F.Carrier) :=
    Rep.of (d.shape.blockTensor (fun i => (d.blocks i).representation))
  have hadm : ∀ i, IsAdmissible (d.blocks i).representation :=
    fun i => (d.tempered i).isAdmissible
  let (i : Fin d.shape.length) :
      Representation.IsIrreducible (d.blocks i).representation := d.irreducible i
  have hπi : Representation.IsIrreducible π.ρ :=
    FiniteTensor.isIrreducible_external (fun i => (d.blocks i).representation)
      (fun i φ =>
        (admissibleSchur_scalarEndomorphism _ (hadm i) (d.irreducible i) φ).exists)
  have hπt : RelativeRegularComparison.IsLeviTempered T d.shape π :=
    (glBlockTensorTempered.{uF, max uF uV} p F T n hn d.shape
      (fun i => d.blocks i) (fun i => (d.blocks i).representation)
      d.irreducible hadm).mp d.tempered
  obtain ⟨Q, R, S, h, ω, v₀, σ, hωi, hωc, hωu, hv₀, hσi, hσsq,
      qFM, qMC, qFC, hqFM, hqMC, hqFC⟩ :=
    glTemperedJointSupport.{uF, max uF uV} p F T n hn d.shape π hπi hπt
  obtain ⟨_m, _hm, _hin, _hout, hhead⟩ :=
    hcomp p F T n hn d.shape Q R S h ω hωi hωc hωu v₀ hv₀ σ hσi hσsq
      ⟨qFM, hqFM⟩ π hπi hπt ⟨qMC, hqMC⟩ ⟨qFC, hqFC⟩
      d.exponent d.strictAnti
  exact RegularHeadExistence.standardModule_hasHead_of_leviTwistHead T d hhead

end RegularHeadExistence

/-- Joint support and analytic tensor temperedness reduce the exact regular-head
target to the supported all-regular relative comparison. -/
theorem glRegularLanglandsHeadExistence_of_relativeRegularComparison
    (hcomp : GLRelativeRegularComparisonStatement.{uF, max uF uV, max uF uV,
      max uF uV}) :
    GLRegularLanglandsHeadExistenceStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn d
  let q := RegularHeadExistence.canonicalHeadOfRelativeRegularComparison.{uF, uV}
    hcomp T hn d
  exact ⟨q.val, q.property⟩

end Langlands
