import Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionProof
import Langlands.Representation.Exponents.TemperedOppositeTwistConeProof
import Langlands.Representation.Classification.TemperedInductionPreservationProof
import Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof
import Langlands.Representation.Twist.LeviImaginaryModCenterProof
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof
import Langlands.Representation.Classification.SupportedRelativeJacquetPositiveBoundProof
import Langlands.Representation.Classification.SupportedAmbientJacquetLengthReductionProof
import Langlands.Representation.Classification.RelativePositiveTotalHeadProof
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.Representation.Exponents.PositiveRootBlockSumsProof
import Langlands.Representation.Exponents.ClosedConeStabilizerRigidityProof

noncomputable section

namespace Langlands

open GeneralLinear Geometric Exponents
open RelativeJacquetMultiplicity RelativeRegularComparison
open scoped BigOperators

universe uF uV uM uW

namespace RelativeRegularComparisonProof

/-! The supported multiplicity comparison follows from the published fixed-branch
obstruction, analytic tempered induction, and weighted cone rigidity. -/

theorem unitaryInduced_tempered
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (D : BlockShape n)
    (σ : Rep.{uM} ℂ (D.Levi F.Carrier))
    (hσirr : Representation.IsIrreducible σ.ρ)
    (hσsq : IsLeviSquareIntegrable T D σ)
    (u : Fin D.length → ℝ) :
    T.IsTempered (ComplexTwistFamilies.unitaryInduced T D σ u).ρ := by
  let := T.topology
  let := T.leviTopologicalGroup D
  let σu := Rep.of
    (T.leviComplexPowerTwist D (fun i => Complex.I * (u i : ℂ)) σ.ρ)
  have htemp : IsLeviTempered T D σ := by
    intro _ _ μ _
    exact isTemperedModCenter_of_squareIntegrable μ (hσsq μ)
  have htempu : IsLeviTempered T D σu :=
    (leviImaginaryTwistModCenter p F T n D σ u).2.mpr htemp
  have hirru : Representation.IsIrreducible σu.ρ :=
    (isIrreducible_twist_iff _ σ.ρ).mpr hσirr
  let Z := D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient D
  let := hμ
  exact glTemperedInductionPreservation.{uF,uM} p F T n hn D μ
    σu.V σu.ρ hirru (htempu μ)

theorem ae_occurrence_forces_blockWeyl
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (Q : BlockRefinement B) (R : BlockRefinement (B.flatten Q))
    (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (ω : Rep.{uV} ℂ (((B.flatten Q).flatten R).Levi F.Carrier))
    (hωirr : Representation.IsIrreducible ω.ρ)
    (hωadm : letI := T.topology; IsAdmissible ω.ρ)
    (hωunit : IsUnitarizable ω.ρ)
    (v₀ : Fin ((B.flatten Q).flatten R).length → ℝ)
    (hv : IsPositiveRootParameter (B.flatten Q) R v₀)
    (σ : Rep.{uM} ℂ ((B.flatten Q).Levi F.Carrier))
    (hσirr : Representation.IsIrreducible σ.ρ)
    (hσsq : IsLeviSquareIntegrable T (B.flatten Q) σ)
    (t : Fin B.length → ℝ) (ht : StrictAnti t)
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier)
      ((B.flatten Q).flatten R) ((B.flatten Q).flatten R) w)
    (hfix : ∀ a : Fin n,
      v₀ (blockIndex ((B.flatten Q).flatten R) (w.symm a)) -
          t (blockIndex B (w.symm a)) =
        v₀ (blockIndex ((B.flatten Q).flatten R) a) - t (blockIndex B a))
    (hae : ∀ᵐ u ∂(MeasureTheory.volume :
        MeasureTheory.Measure (Fin (B.flatten Q).length → ℝ)),
      ComplexTwistFamilies.Occurs T (B.flatten Q)
        ((B.flatten Q).flatten R) ((B.flatten Q).flatten R) σ w hw ω
        (ComplexTwistFamilies.unitaryAmbient (B.flatten Q))
        (ComplexTwistFamilies.refinedMixedAffine (B.flatten Q) R (-v₀)) u) :
    w ∈ blockWeyl B := by
  let := T.topology
  obtain ⟨u, hu⟩ := hae.exists
  have htemp := unitaryInduced_tempered T hn (B.flatten Q) σ hσirr hσsq u
  have hparam :
      ComplexTwistFamilies.refinedMixedAffine (B.flatten Q) R (-v₀) u =
        fun k => -(v₀ k : ℂ) +
          Complex.I * (u (((B.flatten Q).flattenBlockEquiv R).symm k).1 : ℂ) := by
    ext k
    simp only [ComplexTwistFamilies.refinedMixedAffine_apply,
      Pi.neg_apply, Complex.ofReal_neg]
  have hocc : T.IsOppositeJacquetClassExponent ((B.flatten Q).flatten R)
      (ComplexTwistFamilies.unitaryInduced T (B.flatten Q) σ u)
      (Rep.of (CuspidalSupport.transport
        ((B.flatten Q).flatten R) ((B.flatten Q).flatten R) w hw
        (T.leviComplexPowerTwist ((B.flatten Q).flatten R)
          (fun k => -(v₀ k : ℂ) +
            Complex.I * (u (((B.flatten Q).flattenBlockEquiv R).symm k).1 : ℂ))
          ω.ρ))) := by
    simpa only [ComplexTwistFamilies.Occurs,
      ComplexTwistFamilies.unitaryAmbient_apply,
      ComplexTwistFamilies.transported_apply,
      hparam, ComplexTwistFamilies.unitaryInduced_apply] using hu
  have hcone := glTemperedOppositeTwistCone.{uF,uV,max uF uM} p F T n hn
    ((B.flatten Q).flatten R) ((B.flatten Q).flatten R) w hw ω
    hωirr hωadm hωunit v₀
    (fun k => u (((B.flatten Q).flattenBlockEquiv R).symm k).1)
    (ComplexTwistFamilies.unitaryInduced T (B.flatten Q) σ u) htemp hocc
  have hsum : ∀ i : Fin B.length,
      ∑ a : Fin (B.size i),
        v₀ (blockIndex ((B.flatten Q).flatten R) (B.index i a)) = 0 := by
    simpa only [PositiveRootBlockSumsProof.transport_blockIndex] using
      (positiveRootBlockSums.2.2 n B Q R S h v₀ hv)
  have hmem := (closedConeStabilizerRigidity n B
    (fun a => v₀ (blockIndex ((B.flatten Q).flatten R) a))
    t w.symm hsum ht hcone hfix).1
  change w⁻¹ ∈ blockWeyl B at hmem
  simpa only [inv_inv] using (blockWeyl B).inv_mem hmem

theorem transport_irreducible_cuspidal
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} {C E : BlockShape n}
    (h : C = E) (ω : Rep.{uV} ℂ (C.Levi F.Carrier))
    (hωirr : Representation.IsIrreducible ω.ρ)
    (hωcusp : letI := T.topology; CuspidalSupport.IsLeviCuspidal C ω.ρ) :
    letI := T.topology
    Representation.IsIrreducible (h ▸ ω).ρ ∧
      CuspidalSupport.IsLeviCuspidal E (h ▸ ω).ρ := by
  cases h
  exact ⟨hωirr, hωcusp⟩

theorem supported_positive_counts_equal :
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
      letI := T.topology
      ∀ (n : ℕ), 0 < n →
        ∀ (B : BlockShape n) (Q : BlockRefinement B),
        let D := B.flatten Q
        ∀ (R : BlockRefinement D) (S : BlockRefinement B)
          (h : D.flatten R = B.flatten S)
          (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)),
          Representation.IsIrreducible ω.ρ →
          CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ →
          IsUnitarizable ω.ρ →
          ∀ v₀ : Fin (D.flatten R).length → ℝ,
            IsPositiveRootParameter D R v₀ →
            let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
            let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
            ∀ σ : Rep.{uM} ℂ (D.Levi F.Carrier),
              Representation.IsIrreducible σ.ρ → IsLeviSquareIntegrable T D σ →
              (∃ q : (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ,
                Function.Surjective q) →
              ∀ π : Rep.{uW} ℂ (B.Levi F.Carrier),
                Representation.IsIrreducible π.ρ → IsLeviTempered T B π →
                (∃ q : (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ,
                  Function.Surjective q) →
                (∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap π.ρ,
                  Function.Surjective q) →
                ∀ t : Fin B.length → ℝ, StrictAnti t →
                  let τ := fineTwist T B S ωB vB t
                  let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
                  IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
                      (CuspidalJacquetMultiplicity.induced T B πt).ρ.asModule ∧
                    ∃ m : ℕ, 0 < m ∧
                      HasJordanHolderMultiplicity (innerJacquet T B S πt) τ m ∧
                      HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ m := by
  intro p _ F T
  let := T.topology
  dsimp only
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv
    σ hσirr hσsq hqσ π hπirr hπtemp hqmid hqfine t ht
  have hωB := transport_irreducible_cuspidal T h ω hωirr hωcusp
  obtain ⟨hI, _hJ, M, hM⟩ :=
    glSupportedAmbientJacquetLengthReduction p F T n hn
      (CuspidalSupport.cuspidalInductionLength.{uF,uV} F T n) B S (h ▸ ω)
      hωB.1 hωB.2 (h ▸ v₀) π hπtemp.isAdmissible hqfine t
  refine ⟨hI, ?_⟩
  obtain ⟨m, hpos, hmin, hm⟩ :=
    glSupportedRelativeJacquetPositiveBound p F T n hn B S (h ▸ ω)
      hωB.1 hωB.2 (h ▸ v₀) π hπirr hπtemp.isAdmissible hqfine t M hM
  rcases eq_or_lt_of_le hm with heq | hlt
  · subst M
    exact ⟨m, hpos, hmin, hM⟩
  · obtain ⟨w, hw, hout, hfix, hae⟩ :=
      glSupportedRegularMultiplicityBranchObstruction.{uF,uV,uM,uW}
        p F T n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv
        σ hσirr hσsq hqσ π hπirr hπtemp hqmid hqfine t ht m M hmin hM hlt
    exact False.elim (hout
      (ae_occurrence_forces_blockWeyl T hn B Q R S h ω
        hωirr hωcusp.1 hωunit v₀ hv σ hσirr hσsq t ht w hw hfix hae))

end RelativeRegularComparisonProof

open RelativeRegularComparisonProof

/-- The supported inner and ambient Jacquet multiplicities agree at every
regular positive coarse parameter, and the outer standard module has a
strong irreducible head. -/
theorem glRelativeRegularComparison :
    GLRelativeRegularComparisonStatement.{uF,uV,uM,uW} := by
  intro p _ F T
  let := T.topology
  dsimp only
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv
    σ hσirr hσsq hqσ π hπirr hπtemp hqmid hqfine t ht
  obtain ⟨hI, m, hm, hmin, hmamb⟩ :=
    supported_positive_counts_equal p F T n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv
      σ hσirr hσsq hqσ π hπirr hπtemp hqmid hqfine t ht
  refine ⟨m, hm, hmin, hmamb, ?_⟩
  have hπti : Representation.IsIrreducible (T.leviRealPowerTwist B t π.ρ) :=
    (T.isIrreducible_leviRealPowerTwist_iff B t π.ρ).mpr hπirr
  have hπta : IsAdmissible (T.leviRealPowerTwist B t π.ρ) :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr hπtemp.isAdmissible
  exact glRelativePositiveTotalHead.{uF,uV,uW} p F T n hn B S _ _
    hπti hπta hI m hm hmin hmamb

end Langlands
