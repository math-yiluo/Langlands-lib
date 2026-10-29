import Langlands.Representation.Classification.SquareIntegrableExponentStatement
import Langlands.Representation.Classification.SquareIntegrableCentralCharacterProof
import Langlands.Representation.Classification.ProductLeviSquareIntegrableExponentNecessityProof
import Langlands.Representation.Classification.ProductLeviStrictCoefficientL2Proof
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Geometric.SingleBlockJacquetTransport
import Langlands.Group.GL.SingleBlock
import Langlands.Group.GL.OneBlockShape

/-!
# The strict GL exponent criterion

The analytic reductions and the actual single-block normalized Jacquet
comparison identify the strict standard-upper exponent condition with
square integrability modulo the scalar centre, for every Borel Haar measure.
-/

noncomputable section

namespace Langlands

universe uF uV

open GeneralLinear Geometric

namespace SquareIntegrableExponent

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Pull back all-Haar square integrability to any supplied Haar measure on
the actual one-block Levi quotient. -/
private theorem squareIntegrable_singleBlock_pullback
    (hC : C.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hρ : T.IsSquareIntegrable ρ) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure],
      IsSquareIntegrableModCenter (ρ.comp (C.leviEmbedding F.Carrier)) μ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  have := T.generalLinearTopologicalGroup n
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro _ _ μ _
  exact isSquareIntegrableModCenter_comp_continuousMulEquiv ρ
    (C.singleBlockLeviEquivContinuous hC F.Carrier) μ (hρ _)

/-- The product-Levi necessary bound on the actual one-block pullback. -/
private theorem singleBlock_core_of_squareIntegrable
    (hC : C.length = 1) (hn : 0 < n)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hρ : T.IsSquareIntegrable ρ) :
    letI := T.topology
    ∀ (D : BlockRefinement C)
      (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D (ρ.comp (C.leviEmbedding F.Carrier))).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
        (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
          T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
        ‖(ψ a : ℂ)‖ ≤ 1 ∧
          ((∃ (j : Fin C.length) (i k : Fin (D j).length),
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier) ≠
              T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, k⟩) : F.Carrier)) →
            ‖(ψ a : ℂ)‖ < 1) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  have := T.generalLinearTopologicalGroup n
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  let : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    borel _
  have : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := ⟨rfl⟩
  let e := C.singleBlockLeviEquivContinuous hC F.Carrier
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  let := hμ
  let ν := μ.map (centralQuotientCongr e.symm)
  have hν := squareIntegrable_singleBlock_pullback T C hC ρ hρ ν
  exact glProductLeviSquareIntegrableExponentNecessity
    p F T n hn C ν V (ρ.comp (C.leviEmbedding F.Carrier)) hν

open ProductLeviChamber in
/-- The strict chamber bound alone gives the fundamental hypothesis.
The fundamental tuple is nonconstant, so no weak bound on central directions
is needed in this reduction. -/
private theorem strictFundHypothesis_of_strict
    (σ : Representation ℂ (C.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ)
    (hstrict :
      letI := T.topology
      ∀ (D : BlockRefinement C)
        (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet C D σ).comp
            ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
              ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
          (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          (∃ (j : Fin C.length) (i k : Fin (D j).length),
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier) ≠
              T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, k⟩) : F.Carrier)) →
          ‖(ψ a : ℂ)‖ < 1) :
    ProductLeviSquareIntegrable.StrictFundHypothesis T C σ := by
  let := T.topology
  intro s ψ hgen
  apply hstrict (fundRefinement C s) ψ
    (ProductLeviSquareIntegrable.isOpen_ker_of_isGeneralizedEigencharacter_refined
      T C σ hσ _ ψ hgen) hgen
  · intro j
    simp only [flatScalars_apply]
    exact monotone_abs_of_isWeaklyContracting T _ _
      (fundScalars_isStrictlyContracting T C s j).weak
  · have hlen : (fundRefinement C s s.1).length = 2 := by
      rw [fundRefinement, Function.update_self]
      rfl
    refine ⟨s.1, ⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    simp only [flatScalars_apply]
    have h0 : fundScalars T C s s.1 ⟨0, by omega⟩ =
        LocalFactor.PadicAbelian.uniformizerUnit T := by
      simp [fundScalars, twoScalars]
    have h1 : fundScalars T C s s.1 ⟨1, by omega⟩ = 1 := by
      simp [fundScalars, twoScalars]
    rw [h0, h1, uniformizer_abs, Units.val_one, T.normalizedAbs_one]
    exact (inv_lt_one_of_one_lt₀ (residueCardinality_gt_one_real T)).ne

/-- Strict fundamental bounds on the actual one-block Levi give the original
all-Haar analytic predicate, for every admissible carrier and a genuine unitary
central character. -/
private theorem squareIntegrable_of_singleBlock_strictFundHypothesis
    (hC : C.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hadm : letI := T.topology; IsAdmissible ρ)
    (c : letI := T.topology; UnitaryCentralCharacter ρ)
    (hstrict : ProductLeviSquareIntegrable.StrictFundHypothesis T C
      (ρ.comp (C.leviEmbedding F.Carrier))) :
    T.IsSquareIntegrable ρ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  have := T.generalLinearTopologicalGroup n
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  let : MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    borel _
  have : BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) := ⟨rfl⟩
  let e := C.singleBlockLeviEquivContinuous hC F.Carrier
  let σ := ρ.comp e.toMonoidHom
  have hσadm : IsAdmissible σ := isAdmissible_comp_continuousMulEquiv ρ e hadm
  have hcancel : σ.comp e.symm.toMonoidHom = ρ := by
    ext g v
    change ρ (e (e.symm g)) v = ρ g v
    rw [e.apply_symm_apply]
  intro μ _
  have hσ : IsSquareIntegrableModCenter σ (μ.map (centralQuotientCongr e.symm)) := by
    refine ⟨hσadm, c.compContinuousMulEquiv e, ?_⟩
    intro ℓ v
    exact ProductLeviSquareIntegrable.memLp_two_of_strictFundHypothesis
      T C CartanQuotient.cartanCellCount _ σ hσadm hstrict
      (c.compContinuousMulEquiv e) ℓ v
  have hback := isSquareIntegrableModCenter_comp_continuousMulEquiv σ e.symm μ hσ
  rwa [hcancel] at hback

end SquareIntegrableExponent

/-- Casselman's strict exponent criterion for arbitrary nonzero admissible
scalar-character representations of positive-rank `GL_n`. -/
theorem glSquareIntegrableExponentCriterion :
    GLSquareIntegrableExponentCriterionStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ _ ρ ω hadm hω
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  generalize hCdef : CuspidalSupport.LeviAdmissibility.oneBlock n hn = C
  have hC : C.length = 1 := by rw [← hCdef]; rfl
  let := T.leviTopologicalGroup C
  have hcentral := glSquareIntegrableCentralCharacter p F T n hn V ρ ω hadm hω
  constructor
  · intro hs
    refine ⟨hcentral.2.2.1 hs, ?_⟩
    intro B
    obtain ⟨D, rfl⟩ := (C.singleBlockRefinementEquiv hC).surjective B
    intro χ hχ a hmono hne
    let e := C.singleBlockScalarMulEquiv hC D F.Carrierˣ
    let b := e.symm a
    have hb : e b = a := e.apply_symm_apply a
    obtain ⟨hopen, hgen⟩ :=
      (T.singleBlock_isJacquetExponent_iff C hC D ρ χ).mp hχ
    have hmonob :
        ∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
          T.normalizedAbs (b (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier)) :=
      (T.singleBlockScalar_forall_block_monotone_iff C hC D b).mpr (by
        change Monotone (fun i => T.normalizedAbs (e b i : F.Carrier))
        rwa [hb])
    have hneb :
        ∃ (j : Fin C.length) (i k : Fin (D j).length),
          T.normalizedAbs (b (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier) ≠
            T.normalizedAbs (b (C.flattenBlockEquiv D ⟨j, k⟩) : F.Carrier) := by
      rcases hne with ⟨i, k, hik⟩
      refine ⟨C.singleBlockIndex hC, i, k, ?_⟩
      change T.normalizedAbs (e b i : F.Carrier) ≠
        T.normalizedAbs (e b k : F.Carrier)
      rwa [hb]
    have hbound := (SquareIntegrableExponent.singleBlock_core_of_squareIntegrable
      T C hC hn ρ hs D _ hopen hgen b hmonob).2 hneb
    change ‖(χ (e b) : ℂ)‖ < 1 at hbound
    rwa [hb] at hbound
  · rintro ⟨hunit, hexp⟩
    obtain ⟨c⟩ := hcentral.2.1.mpr hunit
    apply SquareIntegrableExponent.squareIntegrable_of_singleBlock_strictFundHypothesis
      T C hC ρ hadm c
    apply SquareIntegrableExponent.strictFundHypothesis_of_strict T C _
      (isSmooth_comp (C.leviEmbedding F.Carrier)
        (C.leviEmbeddingContinuous F.Carrier).continuous hadm.1)
    intro D ψ hopen hgen a hmono hne
    let e := C.singleBlockScalarMulEquiv hC D F.Carrierˣ
    have hχ := (T.singleBlock_isJacquetExponent_iff_flattened C hC D ρ ψ).mp
      ⟨hopen, hgen⟩
    have hmonoa := (T.singleBlockScalar_forall_block_monotone_iff C hC D a).mp hmono
    have hnea : ∃ i k, T.normalizedAbs (e a i : F.Carrier) ≠
        T.normalizedAbs (e a k : F.Carrier) := by
      rcases hne with ⟨j, i, k, hik⟩
      obtain rfl := C.eq_singleBlockIndex hC j
      exact ⟨i, k, hik⟩
    have hbound := hexp _ _ hχ (e a) hmonoa hnea
    change ‖(ψ (e.symm (e a)) : ℂ)‖ < 1 at hbound
    simpa only [e.symm_apply_apply] using hbound

end Langlands
