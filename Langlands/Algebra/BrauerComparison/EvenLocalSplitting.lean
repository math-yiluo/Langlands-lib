import Langlands.Algebra.BrauerComparison.BaseChangeChart
import Langlands.Algebra.BrauerComparison.RelativeTwoTorsion
import Langlands.ClassFieldTheory.Global.GlobalReciprocityProof
import Langlands.ClassFieldTheory.Local.FiniteArtinTransferReduction

/-! # Even-degree splitting of Brauer two-torsion over p-adic fields -/

noncomputable section

open Langlands.LocalClassField
open scoped TensorProduct

namespace Langlands.BrauerComparison

open Langlands.Brauer Langlands.CentralSimple
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (L M : Type u) [Field L] [Field M] [Algebra F.Carrier L] [Algebra F.Carrier M]
  [Algebra L M] [IsScalarTower F.Carrier L M] [FiniteDimensional F.Carrier L]
  [FiniteDimensional F.Carrier M] [FiniteDimensional L M]
  [IsGalois F.Carrier M] [IsGalois L M]
  (A : CSA.{u, u} F.Carrier)

/-- A finite local extension of even degree splits every Brauer class killed by two,
given a common finite Galois splitting chart. -/
theorem isSplit_baseChange_of_even_local_degree
    (e : M ⊗[F.Carrier] A ≃ₐ[M]
      Matrix (Fin (reducedDegree F.Carrier A)) (Fin (reducedDegree F.Carrier A)) M)
    (hA : 2 • classOf A = 0) (hL : 2 ∣ Module.finrank F.Carrier L) :
    IsSplit (baseChange L A) := by
  let d := reducedDegree F.Carrier A
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F.Carrier A)
  let c := relativeInflation F.Carrier M M 2 (relativeClass e)
  let I := localInvariantFamily unramifiedH2Exhaustion p
  have hc : 2 • c = 0 := by
    change 2 • (relativeInflation F.Carrier M M 2).hom (relativeClass e) = 0
    rw [← map_nsmul, two_nsmul_relativeClass_eq_zero e hA, map_zero]
  have hinv : 2 • I.relative F M c = 0 := by rw [← map_nsmul, hc, map_zero]
  have hz := Reciprocity.relativeRestriction_eq_zero_of_dvd I
    (FiniteArtinTransferReduction.canonicalClassFormation (p := p)) F L M c hinv hL
  let e' := baseChangeSplittingChart L M e
  have hzero : relativeClass e' = 0 := (relativeClass_baseChangeSplittingChart L M e).trans hz
  exact ⟨d, reducedDegree_pos F.Carrier A, split_of_relativeClass_eq_zero e' hzero⟩

/-- Local even-degree splitting of Brauer two-torsion in a supplied finite Galois chart. -/
def EvenLocalSplittingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L M : Type u) [Field L] [Field M]
    [Algebra F.Carrier L] [Algebra F.Carrier M] [Algebra L M] [IsScalarTower F.Carrier L M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M] [FiniteDimensional L M]
    [IsGalois F.Carrier M] [IsGalois L M] (A : CSA.{u, u} F.Carrier),
    (M ⊗[F.Carrier] A ≃ₐ[M]
      Matrix (Fin (reducedDegree F.Carrier A)) (Fin (reducedDegree F.Carrier A)) M) →
    2 • classOf A = 0 → 2 ∣ Module.finrank F.Carrier L → IsSplit (baseChange L A)

/-- The local invariant proves the actual splitting at even degree. -/
theorem evenLocalSplitting : EvenLocalSplittingStatement.{u} := by
  intro p _ F L M _ _ _ _ _ _ _ _ _ _ _ A e hA hL
  exact isSplit_baseChange_of_even_local_degree F L M A e hA hL

end Langlands.BrauerComparison
