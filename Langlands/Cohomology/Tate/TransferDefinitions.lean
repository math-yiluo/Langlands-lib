import Langlands.Cohomology.Tate.SubgroupShifts

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The augmentation shift, with its target degree written as a negative natural number. -/
def shiftDownNegativeIso (A : Rep.{u} R G) (n : ℕ) :
    tateCohomology A (-(n + 1 : ℤ)) ≅ tateCohomology (shiftDown A) (-(n : ℤ)) :=
  shiftDownIso A (-(n + 1 : ℤ)) ≪≫
    eqToIso (congrArg (tateCohomology (shiftDown A)) (by omega))

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

/-- The restricted augmentation shift, with the same negative-degree convention. -/
def restrictedShiftDownNegativeIso (A : Rep.{u} R G) (n : ℕ) :
    tateCohomology (Rep.res H.subtype A) (-(n + 1 : ℤ)) ≅
      tateCohomology (Rep.res H.subtype (shiftDown A)) (-(n : ℤ)) :=
  restrictedShiftDownIso H A (-(n + 1 : ℤ)) ≪≫
    eqToIso (congrArg (tateCohomology (Rep.res H.subtype (shiftDown A))) (by omega))

/-- Subgroup restriction in nonnegative degrees, extended through actual connecting isomorphisms. -/
def restrictionNonneg : (n : ℕ) → (A : Rep.{u} R G) →
    tateCohomology A n →ₗ[R] tateCohomology (Rep.res H.subtype A) n
  | 0, A => restrictionZero H A
  | n + 1, A =>
      (restrictedShiftUpIso H A n).toLinearEquiv.toLinearMap.comp
        ((restrictionNonneg n (shiftUp A)).comp (shiftUpIso A n).symm.toLinearEquiv.toLinearMap)

/-- Subgroup corestriction in nonnegative degrees, using the same connecting isomorphisms. -/
def corestrictionNonneg : (n : ℕ) → (A : Rep.{u} R G) →
    tateCohomology (Rep.res H.subtype A) n →ₗ[R] tateCohomology A n
  | 0, A => corestrictionZero H A
  | n + 1, A =>
      (shiftUpIso A n).toLinearEquiv.toLinearMap.comp
        ((corestrictionNonneg n (shiftUp A)).comp
          (restrictedShiftUpIso H A n).symm.toLinearEquiv.toLinearMap)

/-- Subgroup restriction in nonpositive degrees, extended through the augmentation shifts. -/
def restrictionNonpos : (n : ℕ) → (A : Rep.{u} R G) →
    tateCohomology A (-(n : ℤ)) →ₗ[R] tateCohomology (Rep.res H.subtype A) (-(n : ℤ))
  | 0, A => restrictionZero H A
  | n + 1, A =>
      (restrictedShiftDownNegativeIso H A n).symm.toLinearEquiv.toLinearMap.comp
        ((restrictionNonpos n (shiftDown A)).comp
          (shiftDownNegativeIso A n).toLinearEquiv.toLinearMap)

/-- Subgroup corestriction in nonpositive degrees, extended through the augmentation shifts. -/
def corestrictionNonpos : (n : ℕ) → (A : Rep.{u} R G) →
    tateCohomology (Rep.res H.subtype A) (-(n : ℤ)) →ₗ[R] tateCohomology A (-(n : ℤ))
  | 0, A => corestrictionZero H A
  | n + 1, A =>
      (shiftDownNegativeIso A n).symm.toLinearEquiv.toLinearMap.comp
        ((corestrictionNonpos n (shiftDown A)).comp
          (restrictedShiftDownNegativeIso H A n).toLinearEquiv.toLinearMap)

/-- The subgroup restriction constructed by scalar-split dimension shifting in every integer degree. -/
def restriction (A : Rep.{u} R G) : (n : ℤ) →
    tateCohomology A n →ₗ[R] tateCohomology (Rep.res H.subtype A) n
  | .ofNat n => restrictionNonneg H n A
  | .negSucc n => restrictionNonpos H (n + 1) A

/-- The subgroup corestriction constructed by scalar-split dimension shifting in every integer degree. -/
def corestriction (A : Rep.{u} R G) : (n : ℤ) →
    tateCohomology (Rep.res H.subtype A) n →ₗ[R] tateCohomology A n
  | .ofNat n => corestrictionNonneg H n A
  | .negSucc n => corestrictionNonpos H (n + 1) A

end Langlands.Tate
