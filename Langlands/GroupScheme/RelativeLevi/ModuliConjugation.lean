import Langlands.GroupScheme.RelativeLevi.ModuliRestriction
import Langlands.GroupScheme.RelativeLevi.ModuliRepresentation
import Langlands.GroupScheme.CocharacterTransport

/-! # Conjugation of subgroup images commutes with relative restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

open TorusSubgroupModuli

variable {S : Scheme.{u}} {P U : GroupScheme S} {M T : Over S}

/-- The actual point used by the representation interface projects to the
original point under the base-change adjunction. -/
theorem baseChangeBasePointsEquiv_pulledBackPoint (P : GroupScheme S)
    (T : Over S) (g : T ⟶ P.X) :
    baseChangeBasePointsEquiv T.hom P (pulledBackPoint P T g) = g := by
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left]
  exact pullback.lift_fst _ _ _

/-- Pulling a test-valued point into the actual pullback respects its group law. -/
def pulledBackPointHom (P : GroupScheme S) (T : Over S) :
    (T ⟶ P.X) →*
      (Over.mk (𝟙 T.left) ⟶ ((baseChange T.hom).obj P).X) where
  toFun := pulledBackPoint P T
  map_one' := by
    apply (baseChangeBasePointsEquiv T.hom P).injective
    rw [baseChangeBasePointsEquiv_pulledBackPoint, map_one]
  map_mul' g h := by
    apply (baseChangeBasePointsEquiv T.hom P).injective
    rw [baseChangeBasePointsEquiv_pulledBackPoint, map_mul,
      baseChangeBasePointsEquiv_pulledBackPoint,
      baseChangeBasePointsEquiv_pulledBackPoint]

/-- The family point adjunction carries the actual constant family of a
restricted point to the constant family of the original point. -/
theorem familyPointsEquiv_constantPoint (a : T ⟶ M)
    (g : M ⟶ P.X) (V : Over T.left) :
    familyPointsEquiv (G := P) a V
        (((baseChange T.hom).obj P).constantPoint
          (pulledBackPoint P T (a ≫ g)) V) =
      ((baseChange M.hom).obj P).constantPoint
        (pulledBackPoint P M g) ((Over.map a.left).obj V) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [familyPointsEquiv_original]
    simp only [GroupScheme.constantPoint, pulledBackPoint, Over.comp_left,
      Over.homMk_left, Category.assoc, pullback.lift_fst]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

/-- Membership in an actual conjugate can be tested by inverse conjugation. -/
theorem mem_conjugateImage {B : Scheme.{u}} {G : GroupScheme B}
    (g : Over.mk (𝟙 B) ⟶ G.X) (F : SubgroupFunctor G)
    (V : Over B) (x : V ⟶ G.X) :
    x ∈ (conjugateImage g F).carrier V ↔
      (G.constantPoint g V)⁻¹ * x * G.constantPoint g V ∈ F.carrier V := by
  change (∃ y : V ⟶ G.X, y ∈ F.carrier V ∧
    MulAut.conj (G.constantPoint g V) y = x) ↔ _
  simp only [MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have he : (G.constantPoint g V)⁻¹ *
        (G.constantPoint g V * y * (G.constantPoint g V)⁻¹) *
          G.constantPoint g V = y := by group
    rwa [he]
  · intro hx
    refine ⟨_, hx, ?_⟩
    group

/-- Conjugation by a point over a test scheme acts on all subgroup images of
the actual pulled-back group. -/
def conjugateAt (P : GroupScheme S) (T : Over S) (g : T ⟶ P.X)
    (F : SubgroupFunctor ((baseChange T.hom).obj P)) :
    SubgroupFunctor ((baseChange T.hom).obj P) :=
  conjugateImage (pulledBackPoint P T g) F

/-- Actual subgroup restriction commutes with conjugation on every scheme test. -/
theorem restrictImage_conjugateAt (a : T ⟶ M) (g : M ⟶ P.X)
    (F : SubgroupFunctor ((baseChange M.hom).obj P)) :
    restrictImage a (conjugateAt P M g F) =
      conjugateAt P T (a ≫ g) (restrictImage a F) := by
  ext V x
  rw [mem_restrictImage]
  simp only [conjugateAt, mem_conjugateImage, mem_restrictImage,
    map_mul, map_inv, familyPointsEquiv_constantPoint]

/-- The actual points of a supplied group act by conjugation of subgroup
images, using the same pulled-back points as the representation interface. -/
@[instance_reducible]
def subgroupConjugationAction (r : U ⟶ P) (T : Over S) :
    MulAction (T ⟶ U.X) (SubgroupFunctor ((baseChange T.hom).obj P)) where
  smul g F := conjugateAt P T (g ≫ r.hom.hom) F
  one_smul F := by
    change conjugateImage (pulledBackPointHom P T (1 ≫ r.hom.hom)) F = F
    rw [MonObj.one_comp, map_one, conjugateImage_one]
  mul_smul g h F := by
    change conjugateImage (pulledBackPointHom P T ((g * h) ≫ r.hom.hom)) F =
      conjugateImage (pulledBackPointHom P T (g ≫ r.hom.hom))
        (conjugateImage (pulledBackPointHom P T (h ≫ r.hom.hom)) F)
    rw [MonObj.mul_comp, map_mul, conjugateImage_mul]

/-- The supplied group's conjugation action is compatible with restriction. -/
theorem restrictImage_smul (r : U ⟶ P) (a : T ⟶ M) (g : M ⟶ U.X)
    (F : SubgroupFunctor ((baseChange M.hom).obj P)) :
    letI := subgroupConjugationAction r M
    letI := subgroupConjugationAction r T
    restrictImage a (g • F) = (a ≫ g) • restrictImage a F := by
  exact restrictImage_conjugateAt a (g ≫ r.hom.hom) F

end Langlands.GroupScheme.RelativeLevi
