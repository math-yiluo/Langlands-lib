import Langlands.AbelianScheme.Tate.FiniteTorsionClassification
import Langlands.AbelianScheme.Tate.PrimeAdic

/-! # Actual residue-linear torsion structure from divisor cardinalities -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Actual torsion sections are the integer-torsion kernel in the section group. -/
def levelTorsionKernelEquiv (n : ℕ) :
    Level G T n ≃+
      AbelianScheme.Tate.TorsionKernel (Additive (T ⟶ G.X)) n where
  toFun x := ⟨toSection G T n x, by
    change (Additive.toMul x).val ^ n = 1
    exact (mem_levelGroup G T n _).mp (Additive.toMul x).property⟩
  invFun x := Additive.ofMul ⟨Additive.toMul x.val, by
    rw [mem_levelGroup]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Construct actual level coordinates with the pre-existing residue action. -/
def levelLinearEquivOfDivisorCard (n r : ℕ) (hn : 0 < n)
    (hcard : ∀ d : ℕ, d ∣ n → 0 < d → Nat.card (Level G T d) = d ^ r) :
    (Fin r → ZMod n) ≃ₗ[ZMod n] Level G T n := by
  let e := (AbelianScheme.Tate.piZmodTorsionKernelEquivOfDivisorCard
    (Additive (T ⟶ G.X)) n r hn (fun d hd hdpos =>
      (Nat.card_congr (levelTorsionKernelEquiv G T d).toEquiv).symm.trans
        (hcard d hd hdpos))).trans (levelTorsionKernelEquiv G T n).symm
  exact { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }

end Langlands.GroupScheme.Tate
