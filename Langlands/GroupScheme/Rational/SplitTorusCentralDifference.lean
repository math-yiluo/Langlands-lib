import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Unipotent.SplitTorusHom

/-! # Central differences of split-torus homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace AutomorphicAction

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G H : GroupScheme B}
    (i : T.toGrp ⟶ G) (a : characterLattice T)
    (e : AutomorphicAction (Gm B).toGrp G)
    (he : e.restrict (CommGroupScheme.groupHom a) = conjugation i)

include he

/-- A map killed by the descending character has central image, on every test. -/
theorem isCentral_comp_of_character_eq_zero (f : H ⟶ T.toGrp)
    (hf : f ≫ CommGroupScheme.groupHom a = 0) : IsCentral (f ≫ i) := by
  intro U x V b y
  change Commute (b ≫ x ≫ (f ≫ i).hom.hom) y
  have h := congrArg (fun d : AutomorphicAction T.toGrp G =>
    d.act ((b ≫ x) ≫ f.hom.hom) y) he
  simp only [restrict_act, conjugation_act, Grp.comp_hom_hom, Category.assoc] at h ⊢
  have hzero : b ≫ x ≫ f.hom.hom ≫
      (CommGroupScheme.groupHom a).hom.hom = 1 := by
    rw [← Grp.comp_hom_hom, hf]
    change b ≫ x ≫ (1 : H.X ⟶ (Gm B).toGrp.X) = 1
    simp only [MonObj.comp_one]
  rw [hzero, act_one_left] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h.symm)

end AutomorphicAction

namespace Dynamic

section CentralDifference

variable {B : Scheme.{u}} {D G : GroupScheme B}
    (s b : D ⟶ G) (hb : IsCentral b)

/-- Difference from a central homomorphism, as a homomorphism on all tests. -/
def centralDifferencePoints (U : Over B) : (U ⟶ D.X) →* (U ⟶ G.X) where
  toFun x := (x ≫ s.hom.hom) * (x ≫ b.hom.hom)⁻¹
  map_one' := by simp only [MonObj.one_comp, inv_one, mul_one]
  map_mul' x y := by
    simp only [MonObj.mul_comp, mul_inv_rev]
    have hxy := (commute_of_mem_center (hb U x) (y ≫ s.hom.hom)).inv_left
    have hbb := (commute_of_mem_center (hb U x) (y ≫ b.hom.hom)).inv_left.inv_right
    calc
      ((x ≫ s.hom.hom) * (y ≫ s.hom.hom)) *
          ((y ≫ b.hom.hom)⁻¹ * (x ≫ b.hom.hom)⁻¹) =
        ((x ≫ s.hom.hom) * (y ≫ s.hom.hom)) *
          ((x ≫ b.hom.hom)⁻¹ * (y ≫ b.hom.hom)⁻¹) := by rw [hbb.eq]
      _ = ((x ≫ s.hom.hom) * (x ≫ b.hom.hom)⁻¹) *
          ((y ≫ s.hom.hom) * (y ≫ b.hom.hom)⁻¹) :=
        (hxy.mul_mul_mul_comm _ _).symm

theorem centralDifferencePoints_naturality {U V : Over B} (f : V ⟶ U)
    (x : U ⟶ D.X) :
    centralDifferencePoints s b hb V (f ≫ x) =
      f ≫ centralDifferencePoints s b hb U x := by
  change ((f ≫ x) ≫ s.hom.hom) * ((f ≫ x) ≫ b.hom.hom)⁻¹ =
    f ≫ ((x ≫ s.hom.hom) * (x ≫ b.hom.hom)⁻¹)
  simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

/-- The actual difference homomorphism from a central map. -/
def centralDifferenceHom : D ⟶ G :=
  homOfPoints (centralDifferencePoints s b hb)
    (centralDifferencePoints_naturality s b hb)

theorem centralDifferenceHom_apply {U : Over B} (x : U ⟶ D.X) :
    x ≫ (centralDifferenceHom s b hb).hom.hom =
      (x ≫ s.hom.hom) * (x ≫ b.hom.hom)⁻¹ :=
  comp_homOfPoints (centralDifferencePoints s b hb)
    (centralDifferencePoints_naturality s b hb) U x

end CentralDifference

/-- A split-torus map differs trivially from a central map when their
all-test difference lies in an actual affine unipotent subgroup. -/
theorem splitTorus_eq_of_central_difference_unipotent
    {k : Type u} [Field k] {D G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine U.X.left] (hD : IsSplitTorus D) (hU : IsUnipotent U)
    (j : U ⟶ G) (hj : (SubgroupFunctor.range j).IsRepresentedBy j)
    (s b : D ⟶ G) (hb : IsCentral b)
    (hmem : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ D.X),
      (x ≫ s.hom.hom) * (x ≫ b.hom.hom)⁻¹ ∈ (SubgroupFunctor.range j).carrier V) :
    s = b := by
  let d := centralDifferenceHom s b hb
  have hd : SubgroupFunctor.range d ≤ SubgroupFunctor.range j := by
    intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [centralDifferenceHom_apply]
    exact hmem V y
  let dU := hj.factorHom d hd
  have hdU : dU ≫ j = d := hj.factorHom_comp d hd
  have hz : d = 0 := by rw [← hdU, hD.hom_eq_zero_of_isUnipotent hU dU, Limits.zero_comp]
  apply hom_ext_points
  intro V x
  have h := centralDifferenceHom_apply s b hb x
  change x ≫ d.hom.hom = _ at h
  rw [hz] at h
  have h1 : x ≫ (0 : D ⟶ G).hom.hom = 1 := MonObj.comp_one _
  rw [h1] at h
  exact (mul_inv_eq_one.mp h.symm)

end Dynamic

end Langlands.GroupScheme
