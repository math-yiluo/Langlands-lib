import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.Representation.Plancherel.TorusNormKernel.NormCharacter
import Mathlib.RingTheory.Norm.Transitivity

/-! # Character-valuation kernels under finite Galois extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Plancherel.TorusNormKernel

namespace Langlands.Geometry.Building

section FiniteGalois

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {Γk ΓL : Type*} [LinearOrderedCommGroupWithZero Γk]
  [LinearOrderedCommGroupWithZero ΓL]
  (vk : Valuation k Γk) (vL : Valuation L ΓL) [vk.HasExtension vL]
  (hinv : ∀ (σ : L ≃ₐ[k] L) (z : L), vL (σ z) = vL z)

include hinv

/-- For an invariant extension of valuations, a unit-valued field norm forces a
unit-valued element. -/
theorem valuation_eq_one_of_norm_eq_one {z : L}
    (hz : vk (Algebra.norm k z) = 1) : vL z = 1 := by
  classical
  have h := (Valuation.HasExtension.val_map_eq_one_iff vk vL _).mpr hz
  rw [Algebra.norm_eq_prod_automorphisms, map_prod] at h
  simp only [hinv, Finset.prod_const, Finset.card_univ] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (Fintype.card_ne_zero
    (α := L ≃ₐ[k] L))).mp h

/-- Unit values of base-field characters imply unit values of all characters
after a finite Galois extension with invariant valuation. -/
theorem characterValuationKernel_le_comap
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] :
    characterValuationKernel vk G ≤
      (characterValuationKernel vL (baseChanged k L G)).comap
        (rationalExtend k L G) := by
  intro g hg
  change rationalExtend k L G g ∈ characterValuationKernel vL (baseChanged k L G)
  rw [mem_characterValuationKernel] at hg ⊢
  intro χ
  apply valuation_eq_one_of_norm_eq_one vk vL hinv
  rw [← normCharacter_eval χ g]
  exact hg (normCharacter χ)

/-- The character-valuation kernel commutes with finite Galois scalar extension
when the extended valuation is invariant. -/
theorem characterValuationKernel_eq_comap_of_finiteGalois
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] :
    characterValuationKernel vk G =
      (characterValuationKernel vL (baseChanged k L G)).comap
        (rationalExtend k L G) :=
  le_antisymm (characterValuationKernel_le_comap vk vL hinv G)
    (comap_characterValuationKernel_le vk vL G)

/-- Scalar extension restricted to the character-valuation kernels. -/
def characterValuationKernelExtend
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] :
    characterValuationKernel vk G →*
      characterValuationKernel vL (baseChanged k L G) where
  toFun x := ⟨rationalExtend k L G x,
    characterValuationKernel_le_comap vk vL hinv G x.property⟩
  map_one' := Subtype.ext (map_one (rationalExtend k L G))
  map_mul' x y := Subtype.ext ((rationalExtend k L G).map_mul x.val y.val)

@[simp] theorem characterValuationKernelExtend_coe
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    (x : characterValuationKernel vk G) :
    (characterValuationKernelExtend vk vL hinv G x :
      rationalPoints (baseChanged k L G)) = rationalExtend k L G x := rfl

end FiniteGalois

end Langlands.Geometry.Building
