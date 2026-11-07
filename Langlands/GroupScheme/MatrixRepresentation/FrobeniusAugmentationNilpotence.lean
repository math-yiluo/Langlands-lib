import Langlands.GroupScheme.MatrixRepresentation.FrobeniusTopIntegral
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Nilpotence of the actual Frobenius distribution augmentation ideal -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial Finsupp
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusAugmentationNilpotence

open FrobeniusCoordinateModel FrobeniusDistributionAlgebra FrobeniusConvolutionAction
open FrobeniusPolynomialBox FrobeniusTopIntegral TorusUnipotence CoordinateWeights

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

local notation "Q" => quotientAlgebra G p r
local notation "D" => DistributionAlgebra (G := G) p r

/-- Evaluation on the coordinate unit is the genuine distribution augmentation. -/
def augmentation : D →ₐ[k] k :=
  AlgHom.ofLinearMap
    ((LinearMap.applyₗ' (R := k) (S := k) (M := Q) (M₂ := k) 1).comp
      (WithConv.linearEquiv k _).toLinearMap)
    (by
      change Bialgebra.counitAlgHom k Q 1 = 1
      exact map_one _)
    (by
      intro ell1 ell2
      change (ell1 * ell2).ofConv 1 = ell1.ofConv 1 * ell2.ofConv 1
      rw [LinearMap.convMul_apply, Bialgebra.comul_one]
      simp only [Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
        LinearMap.mul'_apply])

@[simp]
theorem augmentation_apply (ell : D) : augmentation p r ell = ell.ofConv 1 := rfl

/-- Its kernel is a two-sided ideal in the actual convolution algebra. -/
abbrev augmentationIdeal : Ideal D := RingHom.ker (augmentation p r)

@[simp]
theorem mem_augmentationIdeal (ell : D) :
    ell ∈ augmentationIdeal (G := G) p r ↔ ell.ofConv 1 = 0 := Iff.rfl

variable {S : CommGroupScheme (Spec (.of k))}
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (ν : cocharacterLattice S)
    {d : ℕ} (w : Fin d → characterLattice S) (t : Fin d → CharacterUnits.Coord G)
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G))
    (htw : ∀ i, t i ∈ CoordinateWeights.weightSpace b (w i))
    (hε : ∀ i, coordCounit G (t i) = 0)
    (hw : ∀ i, 0 < latticePairing S (w i) ν)

local notation "C" => CharacterUnits.Coord G

include hS ht htw hε hw in
/-- Each augmentation factor increases the minimum possible homogeneous height. -/
theorem augmentation_pow_vanishes_on_homogeneous (n : ℕ)
    {ell : D} (hell : ell ∈ augmentationIdeal (G := G) p r ^ (n + 1))
    {χ : characterLattice S} {f : C}
    (hf : f ∈ CoordinateWeights.weightSpace b χ)
    (hχ : latticePairing S χ ν < (n + 1 : ℕ)) :
    ell.ofConv (quotientMap G p r f) = 0 := by
  induction n generalizing ell χ f with
  | zero =>
      simp only [Nat.zero_add, Submodule.pow_one] at hell
      change ell.ofConv 1 = 0 at hell
      exact distribution_eq_zero_on_nonpositive (G := G) p r hS b ν w t ht htw hε hw
        ell hell hf (by norm_num at hχ ⊢; omega)
  | succ n ih =>
      rw [Submodule.pow_succ' (augmentationIdeal (G := G) p r) (by omega : n.succ ≠ 0)] at hell
      refine Submodule.smul_induction_on hell ?_ ?_
      · intro ell1 hell1 ell2 hell2
        change (ell1 * ell2).ofConv (quotientMap G p r f) = 0
        let height : characterLattice S →+ ℤ :=
          ((latticePairing S).flip ν).toAddMonoidHom
        have hker : (⨆ α, Submodule.map₂ (TensorProduct.mk k C C)
            (CoordinateWeights.weightSpace b α) (CoordinateWeights.weightSpace b (χ - α))) ≤
            LinearMap.ker (coordinateContraction p r ell1 ell2) := by
          refine iSup_le fun α => Submodule.map₂_le.2 fun a ha a' ha' => ?_
          change coordinateContraction p r ell1 ell2 (a ⊗ₜ[k] a') = 0
          rw [coordinateContraction_tmul]
          by_cases hα : height α ≤ 0
          · rw [distribution_eq_zero_on_nonpositive (G := G) p r hS b ν w t ht htw hε hw
              ell1 hell1 ha hα, zero_mul]
          · have hβ : height (χ - α) < (n + 1 : ℕ) := by
              rw [map_sub]
              change height χ < (n.succ + 1 : ℕ) at hχ
              push Not at hα
              omega
            rw [ih hell2 ha' hβ, mul_zero]
        rw [convMul_quotientMap]
        exact hker (coordComul_mem_iSup b hS hf)
      · intro ell1 ell2 hell1 hell2
        change ell1.ofConv (quotientMap G p r f) +
          ell2.ofConv (quotientMap G p r f) = 0
        rw [hell1, hell2, zero_add]

include hS ht htw hε hw in
/-- One more than the maximum retained monomial height kills the whole ideal. -/
theorem augmentationIdeal_pow_eq_bot :
    augmentationIdeal (G := G) p r ^ ((latticePairing S (weight w (bound p d r)) ν).toNat + 1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro ell hell
  change ell = 0
  apply WithConv.ofConv_injective
  apply (quotientBasis p r t ht hε).ext
  intro a
  rw [quotientBasis_apply]
  apply augmentation_pow_vanishes_on_homogeneous p r hS b ν w t ht htw hε hw _ hell
    (monomial_mem_weightSpace hS b w t ht htw a.val)
  have hle := box_height_le p r ν w hw a
  omega

include hS ht htw hε hw in
theorem isNilpotent_augmentationIdeal : IsNilpotent (augmentationIdeal (G := G) p r) :=
  ⟨_, augmentationIdeal_pow_eq_bot p r hS b ν w t ht htw hε hw⟩

include hS in
/-- Smooth positive augmentation weights imply nilpotence for the actual dual. -/
theorem isNilpotent_augmentationIdeal_of_positiveWeights
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (hsupp : ∀ χ ∈ CoordinateWeights.support b, 0 < latticePairing S χ ν) :
    IsNilpotent (augmentationIdeal (G := G) p r) := by
  obtain ⟨d, w, t, ht, htw, hε, hw, -⟩ := exists_positiveWeight_coordinates hS b ν hsupp
  exact isNilpotent_augmentationIdeal (G := G) p r hS b ν w t ht htw hε hw

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusAugmentationNilpotence
