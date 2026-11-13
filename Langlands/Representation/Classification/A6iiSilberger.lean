import Langlands.Representation.Classification.RelativeRegularComparisonProof
import Langlands.Representation.Classification.RegularLanglandsHeadComparisonReduction
import Langlands.Representation.Classification.TemperedLeviUpperSupportProof
import Langlands.Representation.Classification.DiscreteSeriesPositiveRootSupportProof
import Langlands.Representation.Classification.SquareIntegrableBlockInductionProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof

/-!
# Silberger's count for explicit segment data

For square-integrable blocks that are quotients of explicit inductions of
twisted supercuspidal representations, the relative Jacquet count of
Silberger 1978, Lemma 5.6, is applied with explicitly constructed fine,
middle and coarse data.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV

section Flattened

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Inner induction from a flattened shape of a block tensor is the block tensor
of the blockwise inductions. -/
theorem nonempty_innerInduced_flatten_equiv {n : ℕ} (B : BlockShape n)
    (Q : BlockRefinement B)
    (Y : ∀ q : (i : Fin B.length) × Fin (Q i).length,
      letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((Q q.1).size q.2) F.Carrier)) :
    letI := T.topology
    Nonempty ((innerInduced T B Q (Rep.of
      (((B.flatten Q).blockTensor fun k =>
        (Y ((B.flattenBlockEquiv Q).symm k)).representation).comp
          (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom))).ρ.Equiv
      (B.blockTensor fun i =>
        ((T.normalizedProductInductionFunctor (Q i)).obj fun j => Y ⟨i, j⟩).representation)) := by
  let := T.topology
  let C : ∀ k : Fin (B.flatten Q).length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten Q).size k) F.Carrier) :=
    fun k => Y ((B.flattenBlockEquiv Q).symm k)
  let H := fun i j =>
    (B.flatten_size_flattenBlockEquiv Q ⟨i, j⟩ ▸
      C (B.flattenBlockEquiv Q ⟨i, j⟩) :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((Q i).size j) F.Carrier))
  have hH (i : Fin B.length) (j : Fin (Q i).length) :
      (H i j).representation.Equiv (Y ⟨i, j⟩).representation :=
    TemperedLeviUpperSupportProof.reindexRankEquiv T
      (fun q : (i : Fin B.length) × Fin (Q i).length => (Q q.1).size q.2)
      Y ((B.flattenBlockEquiv Q).symm_apply_apply ⟨i, j⟩)
  let A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T B Q :=
    fun i => FiniteTensor.externalSmoothObject fun j => Y ⟨i, j⟩
  let eH i :
      (FiniteTensor.external fun j => (H i j).representation).Equiv
        (A i).representation :=
    FiniteTensorFiltration.externalCongr (hH i)
  let Eflat :
      ((B.flatten Q).blockTensor fun k => (C k).representation).Equiv
        ((FiniteTensor.external fun i => (A i).representation).comp
          (flattenedLeviProductEquiv F.Carrier B Q).toMonoidHom) :=
    (FiniteTensor.flattenedTensorRegroupEquiv F T B Q C).trans
      (FiniteTensorFiltration.compCongr
        (FiniteTensorFiltration.externalCongr eH)
        (flattenedLeviProductEquiv F.Carrier B Q).toMonoidHom)
  obtain ⟨⟨Erit, -⟩⟩ := Parabolic.refinedInductionTensor p F T n B Q A
  exact ⟨(ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T B Q
    (ProductLeviCuspidalJacquetAssembly.inducingEquiv T B Q Eflat)).trans Erit⟩

end Flattened

section Cast

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The unitarizing twist cancels in the fine twist after transport along an
equality of fine shapes. -/
theorem fineTwist_cast_cancel (B : BlockShape n) (S : BlockRefinement B) {C : BlockShape n}
    (h : C = B.flatten S) (τ : Rep.{uV} ℂ (C.Levi F.Carrier)) (t₀ : Fin C.length → ℝ)
    (b : Fin B.length → ℝ) :
    fineTwist T B S
        (h ▸ Rep.of (T.leviRealPowerTwist C t₀ τ.ρ) :
          Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
        (h ▸ t₀ : Fin (B.flatten S).length → ℝ) b =
      fineTwist T B S (h ▸ τ : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)) 0 b := by
  subst h
  unfold fineTwist
  congr 1
  change (T.leviRealPowerTwist _ _ (T.leviRealPowerTwist _ t₀ τ.ρ)).comp _ =
    (T.leviRealPowerTwist _ _ τ.ρ).comp _
  rw [← T.leviRealPowerTwist_add]
  congr 2
  funext k
  simp only [Pi.add_apply, Pi.zero_apply, neg_zero, zero_add]
  ring

end Cast

section Count

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

-- The analytic predicate has a nonvacuous Haar specialization giving admissibility.
theorem leviSquareIntegrable_admissible {n : ℕ} (D : BlockShape n)
    (σ : Rep.{uV} ℂ (D.Levi F.Carrier)) (hsq : IsLeviSquareIntegrable T D σ) :
    letI := T.topology
    IsAdmissible σ.ρ := by
  let := T.topology
  let := T.leviTopologicalGroup D
  let Z := D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  obtain ⟨_, _, _, _, hhaar⟩ := (glBlockCentralQuotientTopology p F T n).2 D
  obtain ⟨μ, hμ⟩ := hhaar.1
  let := hμ
  exact (hsq μ).1

set_option maxHeartbeats 1000000 in
/-- Silberger's relative count for explicit data: square-integrable unitarizable
middle blocks `Zs` that are quotients of inductions of supercuspidal blocks `Asc`,
grouped by the outer shape `B` with strictly decreasing exponents `b`. The fine
test representation is the fine twist of the tensor of the `Asc`. -/
theorem silbergerCount {n : ℕ} (hn : 0 < n) (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q))
    (Asc : letI := T.topology
      ∀ q : (k : Fin (B.flatten Q).length) × Fin (R k).length,
        SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (R q.1).size q.2))
    (Zs : letI := T.topology
      ∀ q : (g : Fin B.length) × Fin (Q g).length,
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((Q q.1).size q.2) F.Carrier))
    (hZs : letI := T.topology
      ∀ q, Representation.IsIrreducible (Zs q).representation ∧
        T.IsSquareIntegrable (Zs q).representation ∧ IsUnitarizable (Zs q).representation)
    (qblk : letI := T.topology
      ∀ k : Fin (B.flatten Q).length,
        (T.normalizedProductInductionFunctor (R k)).obj (fun j => (Asc ⟨k, j⟩).obj) ⟶
          Zs ((B.flattenBlockEquiv Q).symm k))
    (hqblk : letI := T.topology; ∀ k, Function.Surjective (SmoothRep.hom (qblk k)))
    (b : Fin B.length → ℝ) (hb : StrictAnti b) :
    letI := T.topology
    let π : Rep.{max uF uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor fun g =>
      ((T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩).representation)
    let πt : Rep.{max uF uV} ℂ (B.Levi F.Carrier) := Rep.of (T.leviRealPowerTwist B b π.ρ)
    let ω₀ : Rep.{max uF uV} ℂ (((B.flatten Q).flatten R).Levi F.Carrier) :=
      Rep.of (((B.flatten Q).flatten R).blockTensor fun k =>
        (Asc (((B.flatten Q).flattenBlockEquiv R).symm k)).obj.representation)
    let S := B.composeRefinement Q R
    let h := B.flatten_composeRefinement Q R
    let τ := fineTwist T B S (h ▸ ω₀ : Rep.{max uF uV} ℂ ((B.flatten S).Levi F.Carrier)) 0 b
    ∃ m : ℕ, 0 < m ∧ HasJordanHolderMultiplicity (innerJacquet T B S πt) τ m ∧
      HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ m ∧
      Classification.HasIrreducibleHead (CuspidalJacquetMultiplicity.induced T B πt).ρ ∧
      Representation.IsIrreducible πt.ρ ∧ IsAdmissible πt.ρ := by
  let := T.topology
  intro π πt ω₀ S h τ
  let D := B.flatten Q
  let fQ := B.flattenBlockEquiv Q
  -- the fine cuspidal data
  obtain ⟨hω₀i, hω₀c⟩ :=
    CuspidalSupport.glCuspidalTensor.{max uF uV, uF} p F T n hn (D.flatten R)
      (fun k => Asc ((D.flattenBlockEquiv R).symm k))
  obtain ⟨t₀, hunit⟩ := leviCuspidalRealUnitarization.{uF, max uF uV} p F T n hn
    (D.flatten R) ω₀.V ω₀.ρ hω₀i hω₀c
  let ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier) :=
    Rep.of (T.leviRealPowerTwist (D.flatten R) t₀ ω₀.ρ)
  have hωi : Representation.IsIrreducible ω.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (D.flatten R) t₀ ω₀.ρ).mpr hω₀i
  have hωc : CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (D.flatten R) t₀ ω₀.ρ).mpr hω₀c
  have hfine : fineTwist T D R ω t₀ 0 = fineTwist T D R ω₀ 0 0 :=
    fineTwist_cast_cancel T D R rfl ω₀ t₀ 0
  have hzero : fineTwist T D R ω₀ 0 0 =
      Rep.of (ω₀.ρ.comp (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom) := by
    unfold fineTwist
    congr 2
    have : (fun k => -(0 : Fin (D.flatten R).length → ℝ) k +
        (0 : Fin D.length → ℝ) ((D.flattenBlockEquiv R).symm k).1) = 0 := by
      funext k
      simp
    rw [this, T.leviRealPowerTwist_zero]
  -- the middle square-integrable data
  have hZadm : ∀ q, IsAdmissible (Zs q).representation := fun q => (hZs q).2.1.isAdmissible
  let σ : Rep.{max uF uV} ℂ (D.Levi F.Carrier) :=
    Rep.of (D.blockTensor fun k => (Zs (fQ.symm k)).representation)
  have : ∀ k, Representation.IsIrreducible (Zs (fQ.symm k)).representation :=
    fun k => (hZs _).1
  have hσi : Representation.IsIrreducible σ.ρ :=
    FiniteTensor.isIrreducible_external (fun k => (Zs (fQ.symm k)).representation)
      (fun k φ =>
        (admissibleSchur_scalarEndomorphism _ (hZadm _) (hZs _).1 φ).exists)
  have hσsq : IsLeviSquareIntegrable T D σ :=
    (glBlockTensorSquareIntegrable.{uF, max uF uV} p F T n hn D (fun k => Zs (fQ.symm k))
      (fun k => (Zs (fQ.symm k)).representation) (fun k => (hZs _).1)
      (fun k => hZadm _)).mp (fun k => (hZs _).2.1)
  have hσadm : IsAdmissible σ.ρ := leviSquareIntegrable_admissible T D σ hσsq
  let := hσi
  have hσnt : Nontrivial σ.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (D.Levi F.Carrier)) σ.ρ.asModule
  -- fine to middle
  obtain ⟨EFM⟩ := nonempty_innerInduced_flatten_equiv T D R (fun q => (Asc q).obj)
  let qext := FiniteTensor.externalMap (fun k => SmoothRep.hom (qblk k))
  have hqext : Function.Surjective qext :=
    FiniteTensor.externalMapSurjectivity _ _ _ _ _ _ _ (fun k => SmoothRep.hom (qblk k)) hqblk
  have hFM : ∃ q : (innerInduced T D R (fineTwist T D R ω t₀ 0)).ρ.IntertwiningMap σ.ρ,
      Function.Surjective q := by
    rw [hfine, hzero]
    exact ⟨qext.comp EFM.toIntertwiningMap, hqext.comp EFM.surjective⟩
  obtain ⟨qFM, hqFM⟩ := hFM
  -- middle to coarse
  obtain ⟨EMC⟩ := nonempty_innerInduced_flatten_equiv T B Q Zs
  let qMC : (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ := EMC.toIntertwiningMap
  have hqMC : Function.Surjective qMC := EMC.surjective
  obtain ⟨qFC, hqFC⟩ :=
    normalizedNestedInduction.{uF, max uF uV, max uF uV, max uF uV}.2
      p F T n B Q R ω t₀ σ π qFM qMC hqFM hqMC
  -- the coarse tempered representation
  have hblocks (g : Fin B.length) :=
    squareIntegrableBlockInduction.{uF, uV} F T (B.size g) (B.positive g) (Q g)
      (fun j => Zs ⟨g, j⟩) (fun j => hZs ⟨g, j⟩)
  have : ∀ g, Representation.IsIrreducible
      ((T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩).representation :=
    fun g => (hblocks g).1
  have hπi : Representation.IsIrreducible π.ρ :=
    FiniteTensor.isIrreducible_external _
      (fun g φ => (admissibleSchur_scalarEndomorphism _ (hblocks g).2.2.isAdmissible
        (hblocks g).1 φ).exists)
  have hπt : IsLeviTempered T B π :=
    (glBlockTensorTempered.{uF, max uF uV} p F T n hn B
      (fun g => (T.normalizedProductInductionFunctor (Q g)).obj fun j => Zs ⟨g, j⟩)
      (fun g => ((T.normalizedProductInductionFunctor (Q g)).obj
        fun j => Zs ⟨g, j⟩).representation)
      (fun g => (hblocks g).1) (fun g => (hblocks g).2.2.isAdmissible)).mp
      (fun g => (hblocks g).2.2)
  -- the positive-root parameter
  have hsourceadm : IsAdmissible (fineTwist T D R ω t₀ 0).ρ :=
    (fineTwistIrreducibleAdmissible p F T n D R ω hωi hωc t₀ 0).2.1
  obtain ⟨χ, hχopen, hχscalar, hχreal⟩ :=
    Exponents.unitaryFineTwistScalarCharacter p F T n D R ω hωi hωc.1 hunit t₀
  have hocc := Exponents.refinedQuotientOppositeCharacter p F T n hn D R
    (fineTwist T D R ω t₀ 0) σ hsourceadm hσadm hσnt χ hχscalar ⟨qFM, hqFM⟩
  have hcone := Exponents.refinedOppositeSquareIntegrableCone p F T n hn D σ
    hσi hσsq R χ hχopen hocc.2 _ hχreal
  have hparam : IsPositiveRootParameter D R t₀ := by
    apply (Exponents.positiveRootParameterCone n D R t₀).mpr
    intro i
    simpa only [neg_mul, neg_neg, D.flatten_size_flattenBlockEquiv R] using hcone i
  obtain ⟨m, hm, hin, hout, hhead⟩ :=
    glRelativeRegularComparison.{uF, max uF uV, max uF uV, max uF uV} p F T n hn B Q R S h
      ω hωi hωc hunit t₀ hparam σ hσi hσsq ⟨qFM, hqFM⟩ π hπi hπt ⟨qMC, hqMC⟩
      ⟨qFC, hqFC⟩ b hb
  have hτ := fineTwist_cast_cancel T B S h ω₀ t₀ b
  have hπa : IsAdmissible π.ρ :=
    FiniteTensor.isAdmissible_external _ (fun g => (hblocks g).2.2.isAdmissible)
  refine ⟨m, hm, ?_, ?_, hhead, (T.isIrreducible_leviRealPowerTwist_iff B b π.ρ).mpr hπi,
    (T.isAdmissible_leviRealPowerTwist_iff B b π.ρ).mpr hπa⟩
  · change HasJordanHolderMultiplicity _ (fineTwist T B S (h ▸ ω₀) 0 b) m
    rw [← hτ]
    exact hin
  · change HasJordanHolderMultiplicity _ (fineTwist T B S (h ▸ ω₀) 0 b) m
    rw [← hτ]
    exact hout

end Count

end Langlands.Classification.A6ii
