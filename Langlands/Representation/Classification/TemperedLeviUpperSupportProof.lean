import Langlands.Representation.Classification.TemperedLeviUpperSupportStatement
import Langlands.Representation.Classification.WholeLeviTemperedFactorizationProof
import Langlands.Representation.Classification.TemperedSupportProof
import Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperProof
import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Classification.BlockTensorSquareIntegrableProof
import Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.Category.UniverseLiftPadic
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Tensor.FiniteProperties

/-!
# Upper discrete-series quotient support for tempered product-Levi representations

Closed ambient support, same-data comparison, and analytic tensor transport
construct the actual upper refined quotient on the original coarse carrier.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeRegularComparison

universe uF uV

namespace TemperedLeviUpperSupportProof

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- Ambient opposite support gives an upper quotient by the published
same-data comparison and square-integrable induction semisimplicity. -/
theorem ambientUpperQuotient
    (n : ℕ) (hn : 0 < n)
    (π : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : π.ρ.IsIrreducible) (ht : T.IsTempered π.ρ) :
    letI := T.topology
    ∃ (Q : BlockShape n) (σ : Rep.{uV} ℂ (Q.Levi F.Carrier)),
      σ.ρ.IsIrreducible ∧ IsLeviSquareIntegrable T Q σ ∧
      ∃ q : (T.normalizedParabolicInduced Q σ.ρ).IntertwiningMap π.ρ,
        Function.Surjective q := by
  let := T.topology
  obtain ⟨Q, W, _, _, σ, hi, hsi, hj⟩ :=
    glTemperedDiscreteSeriesSupport.{uF, uV} p F T n hn π π.ρ hπ ht
  let := T.leviTopologicalGroup Q
  let Z := Q.Levi F.Carrier ⧸ Subgroup.center (Q.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient Q
  let := hμ
  obtain ⟨-, j, hji⟩ :=
    glTemperedDiscreteSeriesOppositeToUpper.{uF, uV, uV}
      p F T n hn Q μ π W π.ρ σ hπ ht hi (hsi μ) hj
  have hss :=
    (isSemisimple_bothInduced_of_squareIntegrable.{uF, uV}
      T Q hn μ σ hi (hsi μ)).1
  obtain ⟨r, hr⟩ := semisimpleRetraction hss j hji
  refine ⟨Q, Rep.of σ, hi, hsi, r, fun v => ⟨j v, ?_⟩⟩
  exact congrArg (fun f : π.ρ.IntertwiningMap π.ρ => f v) hr

/-- Reindexing a dependent rank family carries its representation with it. -/
def reindexRankEquiv {ι : Type} (r : ι → ℕ)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ A i :
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (r j) F.Carrier)).representation.Equiv
      (A j).representation := by
  subst j
  exact Representation.Equiv.refl _

/-- Square-integrable inner-Levi factors assemble to an irreducible
square-integrable representation of the actual flattened Levi. -/
theorem existsFlattenedSquareIntegrable
    (n : ℕ) (hn : 0 < n) (B : BlockShape n) (Q : BlockRefinement B)
    (A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T B Q)
    (hAi : letI := T.topology; ∀ i, (A i).IsIrreducible)
    (hAs : letI := T.topology; ∀ i,
      IsLeviSquareIntegrable T (Q i) (Rep.of (A i).representation)) :
    letI := T.topology
    ∃ σ : Rep.{uV} ℂ ((B.flatten Q).Levi F.Carrier),
      σ.ρ.IsIrreducible ∧ IsLeviSquareIntegrable T (B.flatten Q) σ ∧
      Nonempty (σ.ρ.Equiv
        ((FiniteTensor.external fun i => (A i).representation).comp
          (flattenedLeviProductEquiv F.Carrier B Q).toMonoidHom)) := by
  let := T.topology
  have hfac (i : Fin B.length) :=
    CuspidalSupport.padicLeviAdmissibleFactorization.{uF, uV}
      p F T (B.size i) (B.positive i) (Q i) (A i) (hAi i)
      (IsLeviSquareIntegrable.isAdmissible (T := T) (B := Q i)
        (π := Rep.of (A i).representation) (hAs i))
  choose Y hYi hYa hYe using hfac
  let eY i := (hYe i).some
  have hYs (i : Fin B.length) :
      ∀ j, T.IsSquareIntegrable (Y i j).representation := by
    let := T.leviTopologicalGroup (Q i)
    apply (glBlockTensorSquareIntegrable.{uF, uV} p F T
      (B.size i) (B.positive i) (Q i) (fun j => Y i j)
      (fun j => (Y i j).representation) (hYi i) (hYa i)).mpr
    intro _ _ μ _
    exact isSquareIntegrableModCenter_of_equiv (eY i) μ (hAs i μ)
  let C : ∀ k : Fin (B.flatten Q).length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten Q).size k) F.Carrier) :=
    fun k => Y ((B.flattenBlockEquiv Q).symm k).1
      ((B.flattenBlockEquiv Q).symm k).2
  have hCi : ∀ k, (C k).IsIrreducible :=
    fun k => hYi ((B.flattenBlockEquiv Q).symm k).1
      ((B.flattenBlockEquiv Q).symm k).2
  have hCa : ∀ k, (C k).IsAdmissible :=
    fun k => hYa ((B.flattenBlockEquiv Q).symm k).1
      ((B.flattenBlockEquiv Q).symm k).2
  have hCs : ∀ k, T.IsSquareIntegrable (C k).representation :=
    fun k => hYs ((B.flattenBlockEquiv Q).symm k).1
      ((B.flattenBlockEquiv Q).symm k).2
  let σ : Rep.{uV} ℂ ((B.flatten Q).Levi F.Carrier) :=
    Rep.of ((B.flatten Q).blockTensor fun k => (C k).representation)
  have hσi : σ.ρ.IsIrreducible := by
    let := hCi
    exact FiniteTensor.isIrreducible_external (fun k => (C k).representation)
      (fun k φ =>
        (admissibleSchur_scalarEndomorphism _ (hCa k) (hCi k) φ).exists)
  have hσs : IsLeviSquareIntegrable T (B.flatten Q) σ :=
    (glBlockTensorSquareIntegrable.{uF, uV} p F T n hn (B.flatten Q)
      (fun k => C k) (fun k => (C k).representation) hCi hCa).mp hCs
  let H := fun i j =>
    (B.flatten_size_flattenBlockEquiv Q ⟨i, j⟩ ▸
      C (B.flattenBlockEquiv Q ⟨i, j⟩) :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((Q i).size j) F.Carrier))
  have hH (i : Fin B.length) (j : Fin (Q i).length) :
      (H i j).representation.Equiv (Y i j).representation :=
    reindexRankEquiv T
      (fun q : (i : Fin B.length) × Fin (Q i).length => (Q q.1).size q.2)
      (fun q => Y q.1 q.2) ((B.flattenBlockEquiv Q).symm_apply_apply ⟨i, j⟩)
  let eH i :
      (FiniteTensor.external fun j => (H i j).representation).Equiv
        (A i).representation :=
    (FiniteTensorFiltration.externalCongr (hH i)).trans (eY i).symm
  refine ⟨σ, hσi, hσs, ⟨?_⟩⟩
  exact (FiniteTensor.flattenedTensorRegroupEquiv F T B Q C).trans
    (FiniteTensorFiltration.compCongr
      (FiniteTensorFiltration.externalCongr eH)
      (flattenedLeviProductEquiv F.Carrier B Q).toMonoidHom)

end TemperedLeviUpperSupportProof

/-- Every irreducible analytically tempered product-Levi representation is an
actual quotient of upper refined induction from discrete-series data. -/
theorem glTemperedLeviUpperSupport :
    GLTemperedLeviUpperSupportStatement.{uF, uV} := by
  classical
  intro p _ F T
  let := T.topology
  intro n hn B π hπ ht
  obtain ⟨X, hXi, _, hXt, ⟨eπ⟩⟩ :=
    glWholeLeviTemperedFactorization.{uF, uV} p F T n hn B π hπ ht
  have hblock (i : Fin B.length) :=
    TemperedLeviUpperSupportProof.ambientUpperQuotient T
      (B.size i) (B.positive i) (Rep.of (X i).representation) (hXi i) (hXt i)
  choose Q σ hσi hσs q hq using hblock
  let A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T B Q :=
    fun i => SmoothRep.of (σ i).ρ
      (IsLeviSquareIntegrable.isAdmissible (T := T) (B := Q i)
        (π := σ i) (hσs i)).1
  obtain ⟨σ₀, hσ₀i, hσ₀s, ⟨Eflat⟩⟩ :=
    TemperedLeviUpperSupportProof.existsFlattenedSquareIntegrable T n hn B Q A hσi hσs
  obtain ⟨⟨Erit, -⟩⟩ := Parabolic.refinedInductionTensor p F T n B Q A
  let Emid : (middleInduced T B Q σ₀).ρ.Equiv
      (FiniteTensor.external fun i =>
        T.normalizedParabolicInduced (Q i) (σ i).ρ) :=
    (ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T B Q
      (ProductLeviCuspidalJacquetAssembly.inducingEquiv T B Q Eflat)).trans Erit
  let qtensor := FiniteTensor.externalMap q
  have hqtensor : Function.Surjective qtensor :=
    FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _ q hq
  let q₀ : (middleInduced T B Q σ₀).ρ.IntertwiningMap π.ρ :=
    eπ.symm.toIntertwiningMap.comp (qtensor.comp Emid.toIntertwiningMap)
  have hq₀ : Function.Surjective q₀ :=
    eπ.symm.surjective.comp (hqtensor.comp Emid.surjective)
  let σL : Rep.{max uF uV} ℂ ((B.flatten Q).Levi F.Carrier) :=
    Rep.of (universeLiftRepresentation.{uF} σ₀.ρ)
  let eL : σ₀.ρ.Equiv σL.ρ := universeLiftEquiv.{uF} σ₀.ρ
  have hσLi : σL.ρ.IsIrreducible :=
    (isIrreducible_iff_of_equiv eL).mp hσ₀i
  have hσLs : IsLeviSquareIntegrable T (B.flatten Q) σL := by
    let := T.leviTopologicalGroup (B.flatten Q)
    intro _ _ μ _
    exact isSquareIntegrableModCenter_of_equiv eL μ (hσ₀s μ)
  let EL : (middleInduced T B Q σL).ρ.Equiv
      (middleInduced T B Q σ₀).ρ :=
    ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T B Q
      (FiniteTensorFiltration.compCongr eL.symm
        (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom)
  exact ⟨Q, σL, hσLi, hσLs, q₀.comp EL.toIntertwiningMap,
    hq₀.comp EL.surjective⟩

end Langlands
