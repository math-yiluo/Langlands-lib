import Langlands.GroupScheme.Reductive.CovariantCellRestriction
import Langlands.GroupScheme.Reductive.CoordinateNonZeroDivisor
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.SteinbergRationalCellCriterion
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Rational.TorusUnipotence.StandardUnipotentAction
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.HopfCoordinateComparison
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusCoordinateModel

/-! # Actual opposite-unipotent restriction of entire covariant spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

local notation "λ₀" => CommGroupScheme.groupHom ν ≫ i
local notation "P" => Affine.parabolicScheme λ₀
local notation "U" => Standard.unipotentScheme i (-ν) ∅
local notation "iP" => Affine.parabolicHom λ₀
local notation "iU" => Standard.unipotentHom i (-ν) ∅

local instance : IsAffineHom (Affine.parabolicScheme λ₀).X.hom :=
  (Affine.isClosedSubgroup_parabolicHom λ₀).isAffineHom

variable (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)

include hG hT in
/-- A non-zero-divisor has its full unit locus in the actual `P(ν) · U(-ν)`
cell. The factors exist globally on every relative test scheme. -/
theorem exists_oppositeUnipotentCellCoordinate :
    ∃ q : AffineCoordinates.algebra G,
      q ∈ nonZeroDivisors (AffineCoordinates.algebra G) ∧
      ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X),
        IsUnit (AffineCoordinates.pointAlgebraHom G V g q) →
          ∃ (a : V ⟶ (Affine.parabolicScheme λ₀).X)
            (u : V ⟶ (Standard.unipotentScheme i (-ν) ∅).X),
            g = (a ≫ (Affine.parabolicHom λ₀).hom.hom) *
              (u ≫ (Standard.unipotentHom i (-ν) ∅).hom.hom) := by
  classical
  have := hG.smooth
  have hU : (unipotent (oppositeCocharacter λ₀)).IsRepresentedBy iU := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact Standard.isRepresentedBy_unipotentHom_empty i (-ν) hT
  let m := SubgroupFunctor.cellMultiplication iU iP
  have : IsOpenImmersion m.left :=
    oppositeCellStatement k G λ₀ _ _ iU iP hU
      (Affine.isRepresentedBy_parabolicHom λ₀)
  let e : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let x : G.X.left := (1 : e ⟶ G.X).left (IsLocalRing.closedPoint k)
  have hm1 : CartesianMonoidalCategory.lift 1 1 ≫ m = (1 : e ⟶ G.X) := by
    rw [SubgroupFunctor.lift_cellMultiplication, MonObj.one_comp, MonObj.one_comp, mul_one]
  have hx : x ∈ m.left.opensRange := by
    refine ⟨(CartesianMonoidalCategory.lift (1 : e ⟶ _) (1 : e ⟶ _)).left
      (IsLocalRing.closedPoint k), ?_⟩
    change ((CartesianMonoidalCategory.lift (1 : e ⟶ _) (1 : e ⟶ _)).left ≫ m.left)
      (IsLocalRing.closedPoint k) = x
    rw [← Over.comp_left, hm1]
  obtain ⟨f, hfle, hxf⟩ := (isAffineOpen_top G.X.left).exists_basicOpen_le ⟨x, hx⟩ trivial
  let q₀ : AffineCoordinates.algebra G := (AffineCoordinates.globalAlgEquiv G).symm f
  have hq₀ : AffineCoordinates.globalAlgHom G q₀ = f :=
    (AffineCoordinates.globalAlgEquiv G).apply_symm_apply f
  refine ⟨AffineCoordinates.antipodeCoord G q₀, ?_, ?_⟩
  · have := AffineCoordinates.isDomain_of_isConnectedReductive G hG
    have := AffineCoordinates.nontrivial_algΓ_identityTest (k := k)
    have hunit : IsUnit (AffineCoordinates.pointAlgebraHom G e 1
        (AffineCoordinates.antipodeCoord G q₀)) := by
      rw [AffineCoordinates.pointAlgebraHom_antipode, inv_one,
        AffineCoordinates.isUnit_pointAlgebraHom_iff_range_subset_basicOpen, hq₀]
      have : Subsingleton e.left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim z (IsLocalRing.closedPoint k)]
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    rw [h0, map_zero] at hunit
    exact not_isUnit_zero hunit
  · intro V g hg
    rw [AffineCoordinates.pointAlgebraHom_antipode] at hg
    have hsub := AffineCoordinates.range_point_subset_basicOpen_of_isUnit G g⁻¹ q₀ hg
    rw [hq₀] at hsub
    obtain ⟨a, b, he⟩ := SubgroupFunctor.exists_cell_factors_of_range_subset
      iU iP g⁻¹ (hsub.trans hfle)
    refine ⟨b⁻¹, a⁻¹, ?_⟩
    rw [GrpObj.inv_comp, GrpObj.inv_comp, ← mul_inv_rev, ← he, inv_inv]

variable (χ : AffineCoordinates.algebra (Affine.parabolicScheme
  (CommGroupScheme.groupHom ν ≫ i)))

/-- Restrict the entire actual left-covariant space to the actual opposite
unipotent group and compare the two coordinate presentations. -/
def oppositeUnipotentRestriction :
    AffineCoordinates.leftCovariantSubspace (G := G)
      (H := Affine.parabolicScheme λ₀) (Affine.parabolicHom λ₀) χ →ₗ[k] CharacterUnits.Coord U :=
  (AffineCoordinates.lieCoordinateAlgEquiv U).toLinearEquiv.toLinearMap.comp
    (AffineCoordinates.covariantCellRestriction iP iU χ)

include hG hT in
/-- Full opposite-unipotent restriction is injective, without supplying a cell
or reducing the test schemes to rational points. -/
theorem oppositeUnipotentRestriction_injective :
    Function.Injective (oppositeUnipotentRestriction i ν χ) := by
  obtain ⟨q, hq, hcell⟩ := exists_oppositeUnipotentCellCoordinate i ν hG hT
  exact (AffineCoordinates.lieCoordinateAlgEquiv U).injective.comp
    (AffineCoordinates.covariantCellRestriction_injective iP iU χ hq hcell)

open MatrixRepresentation.FrobeniusCoordinateModel

variable (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The actual entire-space restriction to the Frobenius augmentation quotient.
Its injectivity at a given height is a separate mathematical obligation. -/
def oppositeUnipotentFrobeniusRestriction :
    AffineCoordinates.leftCovariantSubspace (G := G)
      (H := Affine.parabolicScheme λ₀) (Affine.parabolicHom λ₀) χ →ₗ[k] quotientAlgebra U p r :=
  (quotientMap U p r).toLinearMap.comp (oppositeUnipotentRestriction i ν χ)

@[simp]
theorem oppositeUnipotentFrobeniusRestriction_apply
    (f : AffineCoordinates.leftCovariantSubspace (G := G)
      (H := Affine.parabolicScheme λ₀) (Affine.parabolicHom λ₀) χ) :
    oppositeUnipotentFrobeniusRestriction i ν χ p r f =
      quotientMap U p r (oppositeUnipotentRestriction i ν χ f) := rfl

/-- The precise remaining kernel: full restriction lands in the actual
Frobenius image of the augmentation ideal. -/
theorem oppositeUnipotentFrobeniusRestriction_eq_zero_iff
    (f : AffineCoordinates.leftCovariantSubspace (G := G)
      (H := Affine.parabolicScheme λ₀) (Affine.parabolicHom λ₀) χ) :
    oppositeUnipotentFrobeniusRestriction i ν χ p r f = 0 ↔
      oppositeUnipotentRestriction i ν χ f ∈ quotientIdeal U p r := by
  change Ideal.Quotient.mk (quotientIdeal U p r)
    (oppositeUnipotentRestriction i ν χ f) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

end Langlands.GroupScheme.Dynamic
