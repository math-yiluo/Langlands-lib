import Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof
import Langlands.AllField.Representation.CuspidalSupport.LeviTensorReflectionStatement
/-! Supercuspidality reflected by the actual standard-Levi tensor. -/

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicLeviTensorSupercuspidalReflectionStatement padicLeviTensorSupercuspidalReflection
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric

universe uF uW

/-- Proof of the exact published Levi tensor supercuspidality reflection target. -/
theorem padicLeviTensorSupercuspidalReflection :
    PadicLeviTensorSupercuspidalReflectionStatement.{uF, uW} := by
  classical
  intro F _ T n _ B
  let := T.topology
  intro A hirr hadm hqui j
  rw [isSupercuspidal_iff_standard]
  refine ⟨hadm j, ?_⟩
  intro C hC
  let S₀ : BlockRefinement B := fun i =>
    { length := 1
      size := fun _ => B.size i
      positive := fun _ => B.positive i
      sum_eq := by simp }
  let S : BlockRefinement B := Function.update S₀ j C
  have hproper : refinedParabolic F B S ≠ ⊤ := by
    intro htop
    apply hC
    apply top_unique
    intro g _
    have hg : Pi.mulSingle j g ∈ refinedParabolic F B S := by
      rw [htop]
      trivial
    have hgj : (Pi.mulSingle j g : B.Levi F) j ∈
        (S j).parabolic F :=
      hg j (Set.mem_univ j)
    simpa [S] using hgj
  have hN : ∀ i, i ≠ j → (S i).unipotentSubgroup F = ⊥ := by
    intro i hi
    have hSi : S i = S₀ i := by simp [S, hi]
    rw [hSi]
    exact (S₀ i).singleBlock_unipotentSubgroup_eq_bot rfl F
  have hne : ∀ i, i ≠ j → Nontrivial (A i).obj.V := by
    intro i _
    let := hirr i
    exact IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear (B.size i) F)) (A i).representation.asModule
  have h := FiniteTensor.coinvariants_factor_subsingleton
    (fun i => (A i).representation) (fun i => (S i).unipotentSubgroup F)
    j hN hne (hqui S hproper)
  simpa [S] using h

end Langlands.AllField.CuspidalSupport
