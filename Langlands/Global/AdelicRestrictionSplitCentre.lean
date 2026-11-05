import Langlands.Global.AdelicWeilRestrictionArchimedean
import Langlands.Global.AdelicSplitCenterQuotient
import Langlands.Global.RealSplitTorusIdentityComponent
import Langlands.Global.AdelicGroupProduct

/-! # The split-centre subgroup from a rational torus in the Weil restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme Langlands.Global.AdelicWeilRestriction
open PositiveRealTorus

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

/-- Positive real points of `S`, mapped by `j` into the real points of the restriction,
compared with the infinite adelic points of `G`, and included with finite part one. -/
def positiveImageHom :
    orderedCoefficientPositiveSubgroup ℚ S ℝ →* AdelicGroupPoints F G :=
  (AdelicGroupPoints.ofInfinite F G).toMonoidHom.comp
    ((realPointsEquiv F G).toMonoidHom.comp
      ((pointMap ℚ S.toGrp (AffineWeil.groupScheme ℚ F G) ℝ j).comp
        (orderedCoefficientPositiveSubgroup ℚ S ℝ).subtype))

theorem positiveImageHom_apply (a : orderedCoefficientPositiveSubgroup ℚ S ℝ) :
    positiveImageHom F G S j a = AdelicGroupPoints.ofInfinite F G
      (realPointsEquiv F G (pointMap ℚ S.toGrp (AffineWeil.groupScheme ℚ F G) ℝ j a)) :=
  rfl

/-- The image subgroup of the actual adelic points. -/
def subgroup : Subgroup (AdelicGroupPoints F G) :=
  (positiveImageHom F G S j).range

/-- The image together with the principal rational points. -/
def rationalSubgroup : Subgroup (AdelicGroupPoints F G) :=
  subgroup F G S j ⊔ AdelicGroupPoints.rationalSubgroup F G

/-- The actual left homogeneous quotient by the image and the principal rational points. -/
abbrev Quotient := LeftCosetSpace (rationalSubgroup F G S j)

theorem subgroup_le_rationalSubgroup : subgroup F G S j ≤ rationalSubgroup F G S j :=
  le_sup_left

theorem principal_le_rationalSubgroup :
    AdelicGroupPoints.rationalSubgroup F G ≤ rationalSubgroup F G S j :=
  le_sup_right

omit [LocallyOfFiniteType G.X.hom] in
/-- An infinite point that is central stays central after inclusion with finite part one. -/
theorem ofInfinite_mem_center {a : InfiniteAdelicGroupPoints F G}
    (ha : a ∈ Subgroup.center (InfiniteAdelicGroupPoints F G)) :
    AdelicGroupPoints.ofInfinite F G a ∈ Subgroup.center (AdelicGroupPoints F G) := by
  rw [Subgroup.mem_center_iff] at ha ⊢
  intro g
  have hs : AdelicGroupPoints.split F G (AdelicGroupPoints.ofInfinite F G a) = (a, 1) :=
    (AdelicGroupPoints.split F G).apply_symm_apply _
  apply (AdelicGroupPoints.split F G).injective
  rw [map_mul, map_mul, hs]
  exact Prod.ext (ha _) (by simp)

/-- Actual centrality of `j` makes the entire image central in the adelic points. -/
theorem subgroup_le_center (hc : IsCentral j) :
    subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G) := by
  rintro _ ⟨a, rfl⟩
  apply ofInfinite_mem_center
  rw [Subgroup.mem_center_iff]
  intro b
  have h := (commute_of_mem_center (hc _ (a : Lie.AffinePoints S.toGrp ℝ))
    ((realPointsEquiv F G).symm b)).map (realPointsEquiv F G)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.eq.symm

/-- For central `j`, the image is normal, so membership in the combined subgroup is an
actual product of an image point and a principal point. -/
theorem mem_rationalSubgroup_iff (hc : IsCentral j) (x : AdelicGroupPoints F G) :
    x ∈ rationalSubgroup F G S j ↔
      ∃ a : orderedCoefficientPositiveSubgroup ℚ S ℝ, ∃ q : RationalGroupPoints F G,
        positiveImageHom F G S j a * AdelicGroupPoints.rational F G q = x := by
  have : (subgroup F G S j).Normal :=
    Subgroup.normal_of_le_center (subgroup_le_center F G S j hc)
  change x ∈ subgroup F G S j ⊔ AdelicGroupPoints.rationalSubgroup F G ↔ _
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨q, rfl⟩, h⟩
    exact ⟨a, q, h⟩
  · rintro ⟨a, q, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨q, rfl⟩, rfl⟩

end Langlands.Global.RestrictionSplitCentre
