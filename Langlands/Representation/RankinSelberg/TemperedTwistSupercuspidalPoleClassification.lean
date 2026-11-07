import Langlands.Representation.RankinSelberg.IrreducibleComponentEmbedding
import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.SegmentSpecialEssentialSquareIntegrabilityProof
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Category.UniverseLift

/-!
# Classification inputs in the forms used by JPSS (8.2) and (8.4)

Three bridges from the classification of tempered and square-integrable
representations of `GL_n(F)` to the hypotheses of `TemperedLFactorStatement`
(JPSS (8.4)) and `SquareIntegrableLFactorStatement` (JPSS (8.2)):

* an irreducible tempered representation is equivalent to the normalized
  induction of irreducible square-integrable blocks, in the `succBlockShape`
  presentation, assuming `TemperedBlockExhaustion`;
* an irreducible essentially square-integrable representation is an irreducible
  component of the induction of `centeredSegmentBlocks F m π₀` for an irreducible
  supercuspidal `π₀`;
* an irreducible supercuspidal representation is essentially square-integrable.
-/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uG uX uY uF uV uW


section Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A centered supercuspidal segment whose induction contains the supplied
representation as an irreducible component. -/
def HasCenteredSupercuspidalComponent (r : ℕ)
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)) :
    Prop :=
  letI := F.canonicalTopologicalData.topology
  ∃ (a m : ℕ) (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
    (π₀ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)),
    Representation.IsIrreducible π₀.representation ∧
    GeneralLinear.IsSupercuspidal π₀.representation ∧
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F m π₀.representation))
      σ.representation

/-- Exact rank transport keeps essential square-integrability. -/
private theorem isEssentiallySquareIntegrable_of_castRank {r s : ℕ} (h : r = s)
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear r F.Carrier))
    (hA : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable
        (F.canonicalTopologicalData.castRank h A).representation) :
    letI := F.canonicalTopologicalData.topology
    F.canonicalTopologicalData.IsEssentiallySquareIntegrable A.representation := by
  subst h
  exact hA

/-- Bridge to JPSS (8.4). Assuming `TemperedBlockExhaustion` for the canonical
realization, an irreducible tempered representation `τ` of `GL_(k+1)(F)` is
equivalent to the normalized induction, from the standard upper parabolic of
type `(m_1 + 1, …, m_l + 1)`, of irreducible square-integrable unitarizable
blocks `σ_i`. The carrier of `τ` is in `Type uV`; the blocks have carriers in
`Type (max uF uV)`. -/
theorem temperedSquareIntegrableBlockDecomposition
    (exhaustion : Classification.TemperedBlockExhaustion.{uF, uV} F F.canonicalTopologicalData)
    (k : ℕ)
    (τ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear (k + 1) F.Carrier))
    (hτ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible τ.representation)
    (ht : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsTempered τ.representation) :
    letI := F.canonicalTopologicalData.topology
    ∃ (l : ℕ) (m : Fin l → ℕ) (hm : ∑ i, (m i + 1) = k + 1)
      (σ : ∀ i, letI := F.canonicalTopologicalData.topology
        SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier)),
      (∀ i, Representation.IsIrreducible (σ i).representation ∧
        F.canonicalTopologicalData.IsSquareIntegrable (σ i).representation ∧
        IsUnitarizable (σ i).representation) ∧
      Nonempty (τ.representation.Equiv
        (F.canonicalNormalizedProductInduced (succBlockShape m hm)
          (fun i => (σ i).representation))) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let τ' : SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) :=
    SmoothRep.universeLift.{uF} τ
  let eτ : τ.representation.Equiv τ'.representation := SmoothRep.universeLiftEquiv.{uF} τ
  obtain ⟨⟨l, size, pos, sum⟩, σ, hσ, ⟨e⟩⟩ := exhaustion (k + 1) (Nat.succ_pos k) τ'
    ((Langlands.isIrreducible_iff_of_equiv eτ).mp hτ)
    ((PadicField.TopologicalData.isTempered_iff_of_equiv eτ).mp ht)
  obtain ⟨m, rfl⟩ : ∃ m : Fin l → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
  have e2 : τ'.representation.Equiv
      ((T.normalizedProductInductionFunctor (succBlockShape m sum)).obj σ).representation :=
    SmoothRep.equivOfIso e
  have e3 : τ.representation.Equiv
      (T.normalizedProductInduced (succBlockShape m sum) (fun i => (σ i).representation)) :=
    eτ.trans e2
  exact ⟨l, m, sum, σ, hσ, ⟨e3⟩⟩

/-- Core of the bridge to JPSS (8.2), over an arbitrary rank `N`. By the
segment classification, `σ` is the special head of a segment `Δ = [A, …, ν^m A]`
of length `m + 1` with supercuspidal base `A` of `GL_(a+1)(F)`, hence the socle of
the decreasing product `i(ν^m A, …, νA, A)`. Its blocks `ν^(m-i) A` agree with the
centered blocks of `π₀ = ν^(m/2) A`, so the socle embedding composed with the
induced block equivalence exhibits `σ` as a component of the centered induction. -/
private theorem essentiallySquareIntegrable_uniformComponent {N : ℕ} (hN : 0 < N)
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear N F.Carrier))
    (hσ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible σ.representation)
    (hσe : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ.representation) :
    letI := F.canonicalTopologicalData.topology
    ∃ (a m : ℕ) (hsum : ∑ _i : Fin (m + 1), (a + 1) = N)
      (π₀ : letI := F.canonicalTopologicalData.topology
        SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)),
      Representation.IsIrreducible π₀.representation ∧
      GeneralLinear.IsSupercuspidal π₀.representation ∧
      IsIrreducibleComponent
        (F.canonicalTopologicalData.normalizedProductInduced
          (⟨m + 1, fun _ => a + 1, fun _ => Nat.succ_pos a, hsum⟩ : BlockShape N)
          (centeredSegmentBlocks F m π₀.representation))
        σ.representation := by
  let T := F.canonicalTopologicalData
  let := T.topology
  obtain ⟨Δ, h, hhead⟩ :=
    (Classification.segmentEssentialSquareIntegrableClassification.{uF, uV} F T N
      hN σ hσ).mp hσe
  subst h
  rcases Δ with ⟨⟨rk, hrk, cls⟩, L, hL⟩
  obtain ⟨a, rfl⟩ : ∃ a, rk = a + 1 := ⟨rk - 1, (Nat.sub_add_cancel hrk).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
  obtain ⟨A, hA⟩ := Quotient.exists_rep cls
  obtain ⟨-, j, hj, -⟩ := hhead.isIrreducibleSocle_down A hA
  let A' := SupercuspidalRep.twist (T.determinantPowerCharacter (a + 1) ((m : ℝ) / 2))
    (T.isOpen_ker_determinantPowerCharacter (a + 1) ((m : ℝ) / 2))
    (T.ker_determinant_le_ker_determinantPowerCharacter (a + 1) ((m : ℝ) / 2)) A
  have hsum : ∑ _i : Fin (m + 1), (a + 1) = (m + 1) * (a + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  refine ⟨a, m, hsum, A'.obj, A'.property.1, A'.property.2, ?_⟩
  have hblocks : centeredSegmentBlocks F m A'.obj.representation =
      fun i => (T.segmentFactorsDown A.obj (m + 1) hrk i).representation := by
    funext i
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    change realPowerTwist (T.determinantNorm (a + 1)) ((m : ℝ) / 2 - (i : ℕ))
        (realPowerTwist (T.determinantNorm (a + 1)) ((m : ℝ) / 2) A.obj.representation) =
      realPowerTwist (T.determinantNorm (a + 1)) (((m + 1 - 1 - (i : ℕ) : ℕ) : ℝ))
        A.obj.representation
    rw [← realPowerTwist_add]
    congr 1
    rw [Nat.add_sub_cancel, Nat.cast_sub hi]
    ring
  let B := BlockShape.uniform (m + 1) (a + 1) hrk
  have e : ∀ i : Fin B.length, ((T.segmentFactorsDown A.obj (m + 1) hrk i).representation).Equiv
      (centeredSegmentBlocks F m A'.obj.representation i) := fun i => by
    rw [hblocks]
    exact Representation.Equiv.refl _
  obtain ⟨j1, hj1⟩ : ∃ j1 : σ.representation.IntertwiningMap
      ((T.normalizedProductInductionFunctor B).obj
        (T.segmentFactorsDown A.obj (m + 1) hrk)).representation,
      Function.Injective j1 := ⟨j, hj⟩
  obtain ⟨j2, hj⟩ : ∃ j2 : σ.representation.IntertwiningMap
      (T.normalizedProductInduced B
        (fun i => (T.segmentFactorsDown A.obj (m + 1) hrk i).representation)),
      Function.Injective j2 := ⟨j1, hj1⟩
  let E := T.normalizedProductInducedEquiv B e
  let j3 := E.toIntertwiningMap.comp j2
  have hj3 : Function.Injective j3 := E.injective.comp hj
  have key := isIrreducibleComponent_of_injective hσ j3 hj3
  exact key

/-- Bridge to JPSS (8.2). An irreducible essentially square-integrable
representation `σ` of `GL_(r+1)(F)` is an irreducible component of the
normalized induction of `centeredSegmentBlocks F m π₀`, i.e. of
`(π₀ ⊗ α^(m/2), …, π₀ ⊗ α^(-m/2))`, from the standard upper parabolic of type
`(a+1, …, a+1)`, for an irreducible supercuspidal `π₀` of `GL_(a+1)(F)`. In
fact `σ` embeds in that induction. -/
theorem essentiallySquareIntegrableCenteredSegmentComponent (r : ℕ)
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (hσ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible σ.representation)
    (hσe : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ.representation) :
    letI := F.canonicalTopologicalData.topology
    ∃ (a m : ℕ) (hr : ∑ _i : Fin (m + 1), (a + 1) = r + 1)
      (π₀ : letI := F.canonicalTopologicalData.topology
        SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)),
      Representation.IsIrreducible π₀.representation ∧
      GeneralLinear.IsSupercuspidal π₀.representation ∧
      IsIrreducibleComponent
        (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
          (centeredSegmentBlocks F m π₀.representation))
        σ.representation := by
  let T := F.canonicalTopologicalData
  let := T.topology
  obtain ⟨a, m, hsum, π₀, h₁, h₂, h₃⟩ :=
    essentiallySquareIntegrable_uniformComponent.{uF, uV} F (Nat.succ_pos r) σ hσ hσe
  exact ⟨a, m, hsum, π₀, h₁, h₂, h₃⟩

/-- The centered-segment classification supplies the packaged component
certificate without any additional hypothesis. -/
theorem hasCenteredSupercuspidalComponent_of_essentiallySquareIntegrable (r : ℕ)
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (hσ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible σ.representation)
    (hσe : letI := F.canonicalTopologicalData.topology
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ.representation) :
    HasCenteredSupercuspidalComponent F r σ :=
  essentiallySquareIntegrableCenteredSegmentComponent F r σ hσ hσe

/-- An irreducible supercuspidal representation of `GL_(n+1)(F)`, with carrier in
any universe, is essentially square-integrable: it is the special quotient of
its one-term segment. -/
theorem supercuspidal_isEssentiallySquareIntegrable (n : ℕ)
    (π₀ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hirr : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible π₀.representation)
    (hsc : letI := F.canonicalTopologicalData.topology
      GeneralLinear.IsSupercuspidal π₀.representation) :
    letI := F.canonicalTopologicalData.topology
    F.canonicalTopologicalData.IsEssentiallySquareIntegrable π₀.representation := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let π₁ : SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    SmoothRep.universeLift.{uF} π₀
  let e : π₀.representation.Equiv π₁.representation := SmoothRep.universeLiftEquiv.{uF} π₀
  let A : SupercuspidalRep.{uF, max uF uW} (F := F.Carrier) (n := n + 1) :=
    ⟨π₁, (Langlands.isIrreducible_iff_of_equiv e).mp hirr, isSupercuspidal_of_equiv e hsc⟩
  let ρ : PadicField.TopologicalData.CuspidalDatum.{max uF uW, uF} T :=
    ⟨n + 1, Nat.succ_pos n, A.isoClass⟩
  let c := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hquot : T.IsSegmentQuotient (T.singletonSegment ρ)
      (T.castRank (T.singletonSegment_degree ρ).symm A.obj) :=
    ⟨A, rfl, T.isIrreducible_castRank _ A.obj A.property.1, c.toIntertwiningMap,
      c.surjective⟩
  have hess := Classification.segmentSpecialEssentialSquareIntegrability.{uF, uW} F T
    (T.singletonSegment ρ) _ hquot
  exact (PadicField.TopologicalData.isEssentiallySquareIntegrable_iff_of_equiv e).mpr
    (isEssentiallySquareIntegrable_of_castRank F _ A.obj hess)

end Classification

end Langlands.RankinSelberg
