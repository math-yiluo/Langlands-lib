import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.TemperedSupportProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Classification.BlockTensorSquareIntegrableProof
import Langlands.Representation.Classification.SquareIntegrableInductionIrreducibilityProof
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Group.GL.ReverseBlocks

/-!
# Analytic tempered exhaustion by square-integrable blocks

Factor the square-integrable Levi support, construct invariant positive forms,
reverse opposite induction to upper induction, and use irreducibility to turn
the resulting injection into an actual category isomorphism.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear CategoryTheory

universe uF uV

/-- Every irreducible analytically tempered positive-rank representation is
isomorphic to an actual normalized product of irreducible square-integrable
unitarizable blocks. -/
theorem temperedBlockExhaustion
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TemperedBlockExhaustion.{uF, uV} F T := by
  let := T.topology
  intro n hn π hπ htπ
  obtain ⟨B, W, hWadd, hWmodule, σ, hσirr, hσsi, j, hj⟩ :=
    glTemperedDiscreteSeriesSupport.{uF, max uF uV} p F T n hn π
      π.representation hπ htπ
  let := hWadd
  let := hWmodule
  let := T.leviTopologicalGroup B
  have hσadm : IsAdmissible σ := by
    let := borel (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))
    let : BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)) := ⟨rfl⟩
    obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
    let := hμ
    exact (hσsi μ).1
  let S : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of σ hσadm.1
  obtain ⟨A, hAirr, hAadm, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization p F T n hn B S hσirr hσadm
  have hAsi : ∀ i, T.IsSquareIntegrable (A i).representation := by
    apply (glBlockTensorSquareIntegrable.{uF, max uF uV} p F T n hn B
      (fun i => A i) (fun i => (A i).representation) hAirr hAadm).mpr
    intro _ _ μ _
    exact isSquareIntegrableModCenter_of_equiv e μ (hσsi μ)
  have hAform : ∀ i, IsUnitarizable (A i).representation :=
    fun i => glSquareIntegrableUnitarity.{uF, max uF uV} p F T
      (B.size i) (B.positive i) (A i) (A i).representation (hAirr i) (hAsi i)
  let Ar : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (B.reverse.size i) F.Carrier) := fun i => A i.rev
  have hAr : ∀ i, Representation.IsIrreducible (Ar i).representation ∧
      T.IsSquareIntegrable (Ar i).representation ∧ IsUnitarizable (Ar i).representation :=
    fun i => ⟨hAirr i.rev, hAsi i.rev, hAform i.rev⟩
  refine ⟨B.reverse, Ar, hAr, ?_⟩
  let I := (T.normalizedProductInductionFunctor B.reverse).obj Ar
  have hI : Representation.IsIrreducible I.representation :=
    squareIntegrableBlockInductionIrreducibility.{uF, uV} F T n hn B.reverse Ar hAr
  let := T.generalLinearTopologicalGroup n
  let eP : Representation.Equiv (σ.comp (B.oppositeLeviProjection F.Carrier))
      ((B.blockTensor (fun i => (A i).representation)).comp
        (B.oppositeLeviProjection F.Carrier)) :=
    Representation.Equiv.mk e.toLinearEquiv
      (fun g => e.isIntertwining' (B.oppositeLeviProjection F.Carrier g))
  let eInd := Induction.smoothInducedEquiv (B.oppositeParabolic F.Carrier)
    (twistEquiv (T.oppositeParabolicHalfModulus B) eP)
  obtain ⟨eReverse, _⟩ :=
    glOppositeProductReversal.{uF, max uF uV} p F T n B (fun i => A i)
      (fun i => (A i).representation) (fun i => (A i).isSmooth)
  let k : π.representation.IntertwiningMap I.representation :=
    eReverse.toIntertwiningMap.comp (eInd.toIntertwiningMap.comp j)
  have hk : Function.Injective k :=
    eReverse.injective.comp (eInd.injective.comp hj)
  have hkne : k ≠ 0 := by
    obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero π.representation hπ
    intro hz
    apply hv
    apply hk
    simp [hz]
  let := hπ
  let := hI
  have hb : Function.Bijective k :=
    (Representation.IsIrreducible.bijective_or_eq_zero k).resolve_right hkne
  exact ⟨SmoothRep.mkIso (k.ofBijective hb)⟩

end Langlands.Classification
