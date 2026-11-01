import Langlands.Representation.GodementJacquet.FiniteProductMatrixFunctionalEquationStatement
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonTransport
import Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionProof
import Langlands.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof

/-! Finite products, by actual singleton evaluation and first/tail induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF uV uW

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance finiteProductProofTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance finiteProductProofValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance finiteProductProofLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance finiteProductProofMeasurable : MeasurableSpace F.Carrier := borel _
local instance finiteProductProofBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance finiteProductProofT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance finiteProductProofDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance finiteProductProofGLMeasurable (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear r F.Carrier) := borel _
local instance finiteProductProofGLBorel (r : ℕ) : BorelSpace (Langlands.GeneralLinear r F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)

/-- Existence of the full data transports across an actual equivalence. -/
theorem hasNormalizedMatrixFunctionalEquationData_equiv {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (Langlands.GeneralLinear r F.Carrier) V}
    {τ : Representation ℂ (Langlands.GeneralLinear r F.Carrier) W}
    (e : σ.Equiv τ) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν σ ↔
      HasNormalizedMatrixFunctionalEquationData F ψ ν τ := by
  cases r with
  | zero => rfl
  | succ n =>
    change (∃ P PDual c a, NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a) ↔
      ∃ P PDual c a, NormalizedMatrixFunctionalEquationData F ψ ν τ P PDual c a
    constructor
    · rintro ⟨P, PDual, c, a, h⟩
      exact ⟨P, PDual, c, a, (GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
        (q := F.canonicalTopologicalData.residueCardinality) (ψ := ψ) (ν := ν)
        (abv := RankinSelberg.normalizedAbsoluteValue F.canonicalTopologicalData)
        (μ := RankinSelberg.generalLinearHaar F.Carrier n) e).mp h⟩
    · rintro ⟨P, PDual, c, a, h⟩
      exact ⟨P, PDual, c, a, (GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
        (q := F.canonicalTopologicalData.residueCardinality) (ψ := ψ) (ν := ν)
        (abv := RankinSelberg.normalizedAbsoluteValue F.canonicalTopologicalData)
        (μ := RankinSelberg.generalLinearHaar F.Carrier n) e).mpr h⟩

/-- Singleton closure uses the actual single-block evaluation equivalence. -/
private theorem hasData_singleton {r : ℕ} (B : BlockShape r) (hl : B.length = 1)
    (A : ∀ i, SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F.Carrier))
    (hA : ∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (A i).representation) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      (F.canonicalNormalizedProductInduced B (fun i => (A i).representation)) := by
  rcases B with ⟨l, s, hp, hs⟩
  dsimp at hl
  subst l
  have hsize : s = fun _ : Fin 1 => r := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa using hs
  subst s
  let B : BlockShape r := ⟨1, fun _ => r, hp, hs⟩
  have hf : (fun i => ((B.singleBlock_size rfl i).symm ▸ A 0 :
      SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F.Carrier))) = A := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have e := F.canonicalTopologicalData.singleBlockTransportedProductEquiv B rfl (A 0)
  let D := fun AA : ∀ i, SmoothRep.{0,uF,uV} ℂ
    (Langlands.GeneralLinear (B.size i) F.Carrier) =>
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      (F.canonicalNormalizedProductInduced B (fun i => (AA i).representation))
  have hD : D (fun i => ((B.singleBlock_size rfl i).symm ▸ A 0 :
      SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F.Carrier))) :=
    (hasNormalizedMatrixFunctionalEquationData_equiv F ψ ν e).mpr (hA 0)
  exact Eq.mp (congrArg D hf) hD

/-- Apply the published successor-rank two-block theorem to an arbitrary
actual two-block shape, using only equality of its ordered positive sizes. -/
private theorem hasData_twoBlock {r : ℕ} (hr : 0 < r) (B : BlockShape r)
    (hl : B.length = 2)
    (A : ∀ i, SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (B.size i) F.Carrier))
    (hadm : ∀ i, IsAdmissible (A i).representation)
    (hsd : IsSelfDual ψ ν) (ω : Fin B.length → Quasicharacter F.Carrier)
    (hω : ∀ i, Classification.HasGLCentralCharacter F.Carrier (B.size i)
      (A i).representation (ω i).toMonoidHom)
    (hA : ∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (A i).representation) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      (F.canonicalNormalizedProductInduced B (fun i => (A i).representation)) := by
  classical
  cases r with
  | zero => omega
  | succ t =>
    rcases B with ⟨l, s, hp, hs⟩
    dsimp at hl
    subst l
    obtain ⟨m, rfl⟩ : ∃ m : Fin 2 → ℕ, s = fun i => m i + 1 := by
      refine ⟨fun i => s i - 1, funext fun i => ?_⟩
      have := hp i
      dsimp
      omega
    change ∀ i, ∃ P PDual c a,
      NormalizedMatrixFunctionalEquationData F ψ ν (A i).representation P PDual c a at hA
    choose P PDual c a hdata using hA
    exact ⟨_, _, _, _, twoBlockMatrixFunctionalEquationInduction p F t m hs
      (fun i => A i) (fun i => (A i).representation) (fun i => (A i).isSmooth)
      hadm ψ ν hsd ω hω P PDual c a hdata⟩

/-- Induction on the nonempty ordered block family. The tail uses the
original carrier universe; only the outer pair is lifted. -/
private theorem hasData_finite (hsd : IsSelfDual ψ ν) (k : ℕ) :
    ∀ (r : ℕ), 0 < r → ∀ (B : BlockShape r), B.length = k + 1 →
    ∀ (A : ∀ i, SmoothRep.{0,uF,uV} ℂ
      (Langlands.GeneralLinear (B.size i) F.Carrier)),
    (∀ i, IsAdmissible (A i).representation) →
    ∀ (ω : Fin B.length → Quasicharacter F.Carrier),
    (∀ i, Classification.HasGLCentralCharacter F.Carrier (B.size i)
      (A i).representation (ω i).toMonoidHom) →
    (∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (A i).representation) →
    HasNormalizedMatrixFunctionalEquationData F ψ ν
      (F.canonicalNormalizedProductInduced B (fun i => (A i).representation)) := by
  classical
  induction k with
  | zero =>
    intro r _ B hl A _ _ _ hA
    exact hasData_singleton F ψ ν B hl A hA
  | succ k ih =>
    intro r hr B hl A hadm ω hω hA
    let T := F.canonicalTopologicalData
    let tail : SmoothRep.{0,uF,max uF uV} ℂ
        (Langlands.GeneralLinear (B.tailRank hl) F.Carrier) :=
      (T.normalizedProductInductionFunctor (B.tailShape hl)).obj
        (fun j => A (B.tailIndex hl j))
    have htail : HasNormalizedMatrixFunctionalEquationData F ψ ν tail.representation :=
      ih (B.tailRank hl) (B.tailRank_pos hl) (B.tailShape hl) rfl
        (fun j => A (B.tailIndex hl j)) (fun j => hadm (B.tailIndex hl j))
        (fun j => ω (B.tailIndex hl j)) (fun j => hω (B.tailIndex hl j))
        (fun j => hA (B.tailIndex hl j))
    have hadmtail : IsAdmissible tail.representation :=
      Parabolic.normalizedInductionAdmissibility F T (B.tailShape hl) _
        ((B.tailShape hl).blockTensor (fun j => (A (B.tailIndex hl j)).representation))
        (FiniteTensor.isAdmissible_external _ (fun j => hadm (B.tailIndex hl j)))
    let ωtail : Quasicharacter F.Carrier := ∏ j, ω (B.tailIndex hl j)
    have hcharstail : ωtail.toMonoidHom =
        ∏ j, (ω (B.tailIndex hl j)).toMonoidHom := by
      ext a
      simp [ωtail]
      let ev : Quasicharacter F.Carrier →* ℂˣ :=
        { toFun := fun χ => χ a
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have heval : (∏ j, ω (B.tailIndex hl j)) a =
          ∏ j, (ω (B.tailIndex hl j)) a := map_prod ev _ _
      rw [heval]
      simp
    have hωtail : Classification.HasGLCentralCharacter F.Carrier (B.tailRank hl)
        tail.representation ωtail.toMonoidHom := by
      rw [hcharstail]
      exact T.hasScalarCharacter_normalizedProductInduced (B.tailShape hl)
        (fun j => hω (B.tailIndex hl j))
    let C := T.headTailProductFactors B hl A
    let ωC : Fin 2 → Quasicharacter F.Carrier :=
      Fin.cases (ω (B.headIndex hl)) (fun _ => ωtail)
    have hadmC : ∀ i, IsAdmissible (C i).representation := by
      intro i
      fin_cases i
      · exact (SmoothRep.isAdmissible_universeLift_iff (A (B.headIndex hl))).mpr
          (hadm (B.headIndex hl))
      · exact hadmtail
    have hωC : ∀ i, Classification.HasGLCentralCharacter F.Carrier
        ((B.headTailShape hl).size i) (C i).representation (ωC i).toMonoidHom := by
      intro i
      fin_cases i
      · intro a v
        change ULift.up ((A (B.headIndex hl)).representation (GeneralLinear.scalar a)
          v.down) = ULift.up _
        rw [hω (B.headIndex hl) a v.down]
        rfl
      · exact hωtail
    have hC : ∀ i, HasNormalizedMatrixFunctionalEquationData F ψ ν (C i).representation := by
      intro i
      fin_cases i
      · exact (hasNormalizedMatrixFunctionalEquationData_equiv F ψ ν
          (SmoothRep.universeLiftEquiv.{uF} (A (B.headIndex hl)))).mp (hA (B.headIndex hl))
      · exact htail
    have houter := hasData_twoBlock F ψ ν hr (B.headTailShape hl) rfl C hadmC hsd ωC hωC hC
    exact (hasNormalizedMatrixFunctionalEquationData_equiv F ψ ν
      (T.headTailProductInductionEquiv B hl A)).mpr houter

end Padic

/-- Full data exist on the actual finite normalized product if they exist on
its smooth admissible factors with supplied scalar central quasicharacters. -/
theorem finiteProductMatrixFunctionalEquation :
    FiniteProductMatrixFunctionalEquationStatement.{uF,uV} := by
  intro p hp F r hr B A hadm ψ ν hsd ω hω hA
  have hl : B.length ≠ 0 := by
    intro hz
    have hsum : (∑ i, B.size i) = 0 := Finset.sum_eq_zero fun i _ => by
      have := i.isLt
      omega
    have := B.sum_eq
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl
  exact Padic.hasData_finite F ψ ν hsd k r hr B hk A hadm ω hω hA

end Langlands.GodementJacquet
