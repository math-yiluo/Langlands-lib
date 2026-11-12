import Langlands.AlgebraicGeometry.CongruenceChart
import Langlands.GroupScheme.IntegralModel.OpenCongruence
import Langlands.GroupScheme.Absolute.TripleCell

/-! # Actual ordered congruence products from supplied integral open cells -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.CongruenceChart

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The actual positive kernel as the pointed section fibre at any specified
section equal to the identity. Both maps retain the original section. -/
def congruenceKernelSectionFiberEquiv (M : IntegralModel R K G) (n : ℕ+)
    (s : M.integralSections) (hs : s = 1) :
    M.congruenceKernelAt n ≃ sectionFiber R M.group.X n s where
  toFun x := ⟨x.val, by
    apply Over.OverMorphism.ext
    change congruenceBaseMap R n ≫ x.val.left = congruenceBaseMap R n ≫ s.left
    rw [hs]
    apply (baseChangeSectionHom_eq_iff (congruenceBaseMap R n) M.group x.val 1).mp
    exact x.property.trans (map_one (M.reductionAt n)).symm⟩
  invFun x := by
    rcases x with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change M.reductionAt n x = 1
    rw [← map_one (M.reductionAt n)]
    apply (baseChangeSectionHom_eq_iff (congruenceBaseMap R n) M.group x 1).mpr
    have h := congrArg (fun z => z.left) hx
    change congruenceBaseMap R n ≫ x.left = congruenceBaseMap R n ≫ s.left at h
    rwa [hs] at h
  left_inv x := rfl
  right_inv x := rfl

variable (M : IntegralModel R K G)
    (V Z U : GroupScheme (Spec (CommRingCat.of K)))
    (iV : V ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G)

/-- Actual integral models and compatible inclusions for a supplied ordered
three-factor multiplication chart. This structure asserts no existence. -/
structure IntegralTripleCellData where
  negative : IntegralModel R K V
  middle : IntegralModel R K Z
  positive : IntegralModel R K U
  negativeMap : negative.Hom M iV
  middleMap : middle.Hom M iZ
  positiveMap : positive.Hom M iU
  openCell : IsOpenImmersion
    (Dynamic.tripleCellMultiplication negativeMap.hom middleMap.hom positiveMap.hom).left

namespace IntegralTripleCellData

variable {M V Z U iV iZ iU}
    (D : IntegralTripleCellData M V Z U iV iZ iU)

/-- Identify tuples of original congruence sections with the congruence fibre
of their actual integral product scheme at its product identity section. -/
def sourceCongruenceSectionEquiv (n : ℕ+) :
    D.negative.congruenceKernelAt n × D.middle.congruenceKernelAt n ×
        D.positive.congruenceKernelAt n ≃
      sectionFiber R (D.negative.group.X ⊗ (D.middle.group.X ⊗ D.positive.group.X))
        n (lift 1 (lift 1 1)) :=
  ((congruenceKernelSectionFiberEquiv D.negative n 1 rfl).prodCongr
    ((congruenceKernelSectionFiberEquiv D.middle n 1 rfl).prodCongr
      (congruenceKernelSectionFiberEquiv D.positive n 1 rfl))).trans
    ((Equiv.refl _).prodCongr
      (productSectionFiberEquiv
        (1 : D.middle.integralSections) (1 : D.positive.integralSections) n).symm) |>.trans
      (productSectionFiberEquiv (1 : D.negative.integralSections)
        (lift (1 : D.middle.integralSections) (1 : D.positive.integralSections)) n).symm

/-- The actual ordered multiplication from the three positive congruence
kernels is a bijection onto the original target kernel. The integral
multiplication chart itself need not be a group homomorphism. -/
def congruenceProductEquiv (n : ℕ+) :
    D.negative.congruenceKernelAt n × D.middle.congruenceKernelAt n ×
        D.positive.congruenceKernelAt n ≃ M.congruenceKernelAt n := by
  let c := Dynamic.tripleCellMultiplication
    D.negativeMap.hom D.middleMap.hom D.positiveMap.hom
  let : IsOpenImmersion c.left := D.openCell
  let s : M.integralSections := lift 1 (lift 1 1) ≫ c
  have hs : s = 1 := by
    dsimp only [s, c]
    rw [Dynamic.lift_tripleCellMultiplication]
    change rationalPoints.map D.negativeMap.hom 1 *
      (rationalPoints.map D.middleMap.hom 1 * rationalPoints.map D.positiveMap.hom 1) = 1
    rw [map_one, map_one, map_one, one_mul, one_mul]
  exact (D.sourceCongruenceSectionEquiv n).trans
    ((openSectionFiberEquiv c (lift 1 (lift 1 1)) n).trans
      (congruenceKernelSectionFiberEquiv M n s hs).symm)

@[simp] theorem congruenceProductEquiv_val (n : ℕ+)
    (t : D.negative.congruenceKernelAt n × D.middle.congruenceKernelAt n ×
      D.positive.congruenceKernelAt n) :
    (D.congruenceProductEquiv n t).val =
      rationalPoints.map D.negativeMap.hom t.1.val *
        rationalPoints.map D.middleMap.hom t.2.1.val *
        rationalPoints.map D.positiveMap.hom t.2.2.val := by
  change lift t.1.val (lift t.2.1.val t.2.2.val) ≫
      Dynamic.tripleCellMultiplication D.negativeMap.hom D.middleMap.hom D.positiveMap.hom =
    _
  rw [Dynamic.lift_tripleCellMultiplication]
  exact (mul_assoc _ _ _).symm

/-- Existence and uniqueness of the same ordered product, stated directly on
the original integral sections. -/
theorem ordered_congruence_product_bijective (n : ℕ+) :
    Function.Bijective (fun
      t : D.negative.congruenceKernelAt n × D.middle.congruenceKernelAt n ×
        D.positive.congruenceKernelAt n =>
      (⟨rationalPoints.map D.negativeMap.hom t.1.val *
          rationalPoints.map D.middleMap.hom t.2.1.val *
          rationalPoints.map D.positiveMap.hom t.2.2.val,
        (M.congruenceKernelAt n).mul_mem
          ((M.congruenceKernelAt n).mul_mem
            (D.negativeMap.map_mem_congruenceKernelAt n t.1.property)
            (D.middleMap.map_mem_congruenceKernelAt n t.2.1.property))
          (D.positiveMap.map_mem_congruenceKernelAt n t.2.2.property)⟩ :
        M.congruenceKernelAt n)) := by
  constructor
  · intro a b hab
    apply (D.congruenceProductEquiv n).injective
    apply Subtype.ext
    simpa only [D.congruenceProductEquiv_val] using congrArg Subtype.val hab
  · intro x
    obtain ⟨t, ht⟩ := (D.congruenceProductEquiv n).surjective x
    refine ⟨t, ?_⟩
    exact (Subtype.ext (D.congruenceProductEquiv_val n t)).symm.trans ht

end IntegralTripleCellData
end Langlands.GroupScheme.IntegralModel
