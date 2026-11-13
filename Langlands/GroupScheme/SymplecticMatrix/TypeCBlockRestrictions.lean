import Langlands.GroupScheme.Quaternionic.DegreeSplittingTorus
import Langlands.GroupScheme.SymplecticMatrix.TypeCPinningSimpleRoots
import Langlands.LinearAlgebra.TypeCBlockWeights

/-! # Simple type C restrictions along a prescribed block torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Quaternionic.DegreeSplitting SymplecticMatrix

/-- Restriction along the repeated-block torus, expressed in integer coordinates. -/
def typeCBlockRestriction (k : Type u) [Field k] (degree r n : ℕ) :
    characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k))
      (ULift.{u} (Fin n))) →+ (Fin r → ℤ) where
  toFun χ := GeneralLinear.characterCoordEquiv (Fin r) k
    (blockTorusHom k degree r n ≫ χ)
  map_zero' := by simp
  map_add' χ ψ := by simp [Preadditive.comp_add]

/-- A simple type C character restricts to the corresponding repeated-block vector. -/
theorem typeCBlockRestriction_simple {k : Type u} [Field k] {degree r n : ℕ}
    (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k))
      (ULift.{u} (Fin n)))) (i : Fin n)
    (hχ : GeneralLinear.characterCoordEquiv (Fin n) k χ =
      weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (TypeCPinning.simpleSnd i)) :
    typeCBlockRestriction k degree r n χ = TypeCBlockWeights.simpleRestriction degree r i := by
  classical
  have hchar : χ = if h : i.val + 1 < n then
      coordChar (Fin n) k i - coordChar (Fin n) k ⟨i.val + 1, h⟩
      else 2 • coordChar (Fin n) k i := by
    apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
    rw [hχ, TypeCPinning.weightCoord_inl_sub_simpleSnd]
    split_ifs with hi
    · rw [map_sub, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar]
    · rw [map_nsmul, characterCoordEquiv_coordChar]
      funext a
      simp [Pi.single_apply]
  have hcoord (a : Fin n) :
      typeCBlockRestriction k degree r n (coordChar (Fin n) k a) =
        TypeCBlockWeights.weight degree r a.val :=
    characterCoordEquiv_blockTorusHom_comp_coordChar k degree r n a
  rw [hchar]
  unfold TypeCBlockWeights.simpleRestriction
  split_ifs with hi
  · rw [map_sub, hcoord, hcoord]
  · rw [map_nsmul, hcoord]

end Langlands.GroupScheme
