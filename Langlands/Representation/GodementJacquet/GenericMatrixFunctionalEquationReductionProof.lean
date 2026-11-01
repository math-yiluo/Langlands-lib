import Langlands.Representation.GodementJacquet.FiniteProductMatrixFunctionalEquationProof
import Langlands.Representation.GodementJacquet.SubquotientFunctionalEquationDescent
import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationReductionStatement
import Langlands.Representation.GodementJacquet.TateMatrixFunctionalEquationStatement
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationStatement
import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.Representation.Smooth.Schur.Proof

/-! Conditional irreducible reduction from the two full analytic bases. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF uV uW

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance genericMatrixReductionTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance genericMatrixReductionValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance genericMatrixReductionLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance genericMatrixReductionMeasurable : MeasurableSpace F.Carrier := borel _
local instance genericMatrixReductionBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance genericMatrixReductionT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance genericMatrixReductionDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance genericMatrixReductionGLMeasurable (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear r F.Carrier) := borel _
local instance genericMatrixReductionGLBorel (r : ℕ) : BorelSpace (Langlands.GeneralLinear r F.Carrier) := ⟨rfl⟩

/-- Restrict the actual smooth Schur character to scalar matrices. -/
private theorem exists_scalarQuasicharacter {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear r F.Carrier) V)
    (ha : IsAdmissible σ) (hi : σ.IsIrreducible) :
    ∃ ω : Quasicharacter F.Carrier,
      Classification.HasGLCentralCharacter F.Carrier r σ ω.toMonoidHom := by
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup r
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter σ ha hi
  let ω : Quasicharacter F.Carrier :=
    ⟨χ.comp GeneralLinear.scalarToCenter,
      hlc.continuous.comp (GeneralLinear.scalarContinuous.continuous.subtype_mk _)⟩
  exact ⟨ω, fun a v => hact (GeneralLinear.scalarToCenter a) v⟩

/-- Apply the rank-one or higher-rank supercuspidal analytic base. -/
private theorem hasData_supercuspidal
    (hTate : TateMatrixFunctionalEquationStatement.{uF,uV})
    (hSuper : SupercuspidalMatrixFunctionalEquationStatement.{uF,uV})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    {r : ℕ} (hr : 0 < r)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear r F.Carrier) V)
    (hσ : IsSupercuspidal σ) (hi : σ.IsIrreducible) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν σ := by
  cases r with
  | zero => omega
  | succ s =>
    cases s with
    | zero => exact hTate p F ψ ν hsd V σ hσ.1 hi
    | succ t =>
      obtain ⟨c, a, h⟩ := hSuper p F ψ ν hsd t V σ hσ hi
      exact ⟨1, 1, c, a, h⟩

/-- A genuine injection exhibits the source as an actual subquotient. -/
private theorem hasData_of_injective {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (j : σ.IntertwiningMap τ) (hj : Function.Injective j) (hτ : IsSmooth τ)
    (hdata : HasNormalizedMatrixFunctionalEquationData F ψ ν τ) :
    HasNormalizedMatrixFunctionalEquationData F ψ ν σ := by
  let jR : σ.IntertwiningMap j.range.toRepresentation :=
    { toLinearMap := j.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun f : V →ₗ[ℂ] W => f v) (j.isIntertwining' g) }
  have hbij : Function.Bijective jR := by
    constructor
    · intro v w h
      exact hj (congrArg Subtype.val h)
    · rintro ⟨w, v, rfl⟩
      exact ⟨v, rfl⟩
  let e := jR.ofBijective hbij
  obtain ⟨P, PDual, c, a, h⟩ := hdata
  exact normalizedMatrixFunctionalEquationData_of_subquotient F ψ ν hsd hτ
    j.range e.symm.toIntertwiningMap e.symm.surjective h

end Padic

/-- Reduce the unchanged generic statement to the two unchanged analytic bases. -/
theorem genericMatrixFunctionalEquationReduction :
    GenericMatrixFunctionalEquationReductionStatement.{uF,uV} := by
  intro hTate hSuper p hp F ψ ν hsd n V _ _ σ hσ hi
  classical
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  let : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
  let : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  let : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)) σ.asModule
  let A : SmoothRep.{0,uF,uV} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    SmoothRep.of σ hσ.1.1
  obtain ⟨B, C, j, hj⟩ :=
    Classification.irreducible_supercuspidalProduct_embedding.{uF,uV,uV}
      F F.canonicalTopologicalData (n + 1) (Nat.succ_pos n) A hi
  choose ω hω using fun i =>
    Padic.exists_scalarQuasicharacter F (C i).obj.representation
      (C i).property.2.1 (C i).property.1
  have hC : ∀ i, Padic.HasNormalizedMatrixFunctionalEquationData F ψ ν
      (C i).obj.representation := fun i =>
    Padic.hasData_supercuspidal F hTate hSuper ψ ν hsd
      (B.positive i) (C i).obj.representation (C i).property.2 (C i).property.1
  have hprod := finiteProductMatrixFunctionalEquation p F (n + 1)
    (Nat.succ_pos n) B (fun i => (C i).obj) (fun i => (C i).property.2.1)
    ψ ν hsd ω hω hC
  have hsmooth : IsSmooth
      (F.canonicalNormalizedProductInduced B (fun i => (C i).obj.representation)) :=
    ((F.canonicalTopologicalData.normalizedProductInductionFunctor B).obj
      (fun i => (C i).obj)).isSmooth
  exact Padic.hasData_of_injective F ψ ν hsd j hj hsmooth hprod

end Langlands.GodementJacquet
