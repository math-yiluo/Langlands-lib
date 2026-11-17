import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.Absolute.BorelCentralizerCenterStatement
import Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityStatement
import Langlands.GroupScheme.PointCentralizer
import Langlands.AlgebraicGeometry.AffinePointGluing

/-! # Borel centralizer equality from homomorphism rigidity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General

variable {S : Scheme.{u}} {B G : GroupScheme S} (i : B ⟶ G)

/-- Restriction to the image of `i` detects endomorphisms after every affine base
change. This is a condition, with no assertion that a given `i` satisfies it. -/
def AffineEndomorphismRestrictionRigidity : Prop :=
  ∀ (A : CommRingCat.{u}) (b : Spec A ⟶ S)
    (φ₁ φ₂ : (GroupScheme.baseChange b).obj G ⟶ (GroupScheme.baseChange b).obj G),
    (GroupScheme.baseChange b).map i ≫ φ₁ = (GroupScheme.baseChange b).map i ≫ φ₂ →
      φ₁ = φ₂

/-- A central point of a group maps into the centralizer of its image. -/
theorem center_map_mem_centralizer_range {T : Over S} {x : T ⟶ B.X}
    (hx : x ∈ (center B).carrier T) :
    x ≫ i.hom.hom ∈ (SubgroupFunctor.range i).centralizer.carrier T := by
  rintro V a _ ⟨y, rfl⟩
  have h := (hx V a y).map ((yonedaGrp.map i).app (Opposite.op V)).hom
  change Commute ((a ≫ x) ≫ i.hom.hom) (y ≫ i.hom.hom) at h
  change Commute (a ≫ x ≫ i.hom.hom) (y ≫ i.hom.hom)
  simpa only [Category.assoc] using h

/-- If restriction to a subgroup detects endomorphisms after a base change, a point
centralizing that subgroup commutes with every point over that base. -/
theorem commute_of_baseChange_restriction_rigidity {S' : Scheme.{u}} (b : S' ⟶ S)
    (hres : ∀ (φ₁ φ₂ : (GroupScheme.baseChange b).obj G ⟶
        (GroupScheme.baseChange b).obj G),
      (GroupScheme.baseChange b).map i ≫ φ₁ = (GroupScheme.baseChange b).map i ≫ φ₂ →
        φ₁ = φ₂)
    {x y : Over.mk b ⟶ G.X}
    (hx : x ∈ (SubgroupFunctor.range i).centralizer.carrier (Over.mk b)) : Commute x y := by
  let G' := (GroupScheme.baseChange b).obj G
  let x' := (baseChangeBasePointsEquiv b G).symm x
  have hi : (GroupScheme.baseChange b).map i ≫ (G'.innerIso x').hom =
      (GroupScheme.baseChange b).map i := by
    apply hom_ext_points
    intro T z
    apply (baseChangePointsEquiv b G T).injective
    change baseChangePointsEquiv b G T
      ((z ≫ ((GroupScheme.baseChange b).map i).hom.hom) ≫
        (G'.innerIso x').hom.hom.hom) = _
    rw [comp_innerIso_hom, map_mul, map_mul, map_inv,
      baseChangePointsEquiv_comp, baseChangePointsEquiv_constantPoint_symm]
    have h := hx ((Over.map b).obj T)
      (Over.homMk T.hom (by simp))
      (baseChangePointsEquiv b B T z ≫ i.hom.hom) ⟨_, rfl⟩
    rw [h.eq, mul_inv_cancel_right]
  have he : (G'.innerIso x').hom = 𝟙 G' := hres _ _ (by
    rw [Category.comp_id]
    exact hi)
  let y' := (baseChangeBasePointsEquiv b G).symm y
  have hy := congrArg (fun f : G' ⟶ G' => y' ≫ f.hom.hom) he
  have hxy : x' * y' * x'⁻¹ = y' := by
    change y' ≫ (G'.innerIso x').hom.hom.hom = y' ≫ 𝟙 G'.X at hy
    rw [comp_innerIso_hom, constantPoint_self, Category.comp_id] at hy
    exact hy
  have h := congrArg (baseChangeBasePointsEquiv b G) hxy
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, x', y'] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- Endomorphism rigidity on all affine base changes implies equality of the all-test
centralizer of the subgroup and the centre. -/
theorem centralizer_range_eq_center_of_affine_restriction_rigidity
    (hres : AffineEndomorphismRestrictionRigidity i) :
    (SubgroupFunctor.range i).centralizer = center G := by
  apply le_antisymm
  · intro T x hx V a y
    change (a ≫ x) * y = y * (a ≫ x)
    apply Over.OverMorphism.ext
    apply V.left.affineCover.hom_ext
    intro j
    let U : Over S := Over.mk (V.left.affineCover.f j ≫ V.hom)
    let c : U ⟶ V := Over.homMk (V.left.affineCover.f j)
    have hc := commute_of_baseChange_restriction_rigidity i U.hom
      (hres _ U.hom) ((SubgroupFunctor.range i).centralizer.comp_mem (c ≫ a) hx)
      (y := c ≫ y)
    have hh : c ≫ ((a ≫ x) * y) = c ≫ (y * (a ≫ x)) := by
      simpa only [MonObj.comp_mul, ← Category.assoc] using hc.eq
    exact congrArg (fun f => f.left) hh
  · exact SubgroupFunctor.center_le_centralizer _

end General

/-- Milne 17.22 follows from the exact algebra-base homomorphism rigidity statement 17.21. -/
theorem borelCentralizerCenter_of_homomorphismRigidity
    (hrig : BorelHomomorphismRigidityStatement.{u}) :
    BorelCentralizerCenterStatement.{u} := by
  intro k _ _ G _ _ _ B i hi
  refine ⟨fun T x hx => center_map_mem_centralizer_range i hx, ?_⟩
  apply centralizer_range_eq_center_of_affine_restriction_rigidity
  intro A b
  let : Algebra k A := Langlands.AlgebraicGeometry.AffinePoints.algebraOfHom b
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k A)) = b :=
    Langlands.AlgebraicGeometry.AffinePoints.specMap_algebraMap_algebraOfHom b
  have h := hrig k G G B i hi A
  change ∀ (φ₁ φ₂ :
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k A)))).obj G ⟶
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k A)))).obj G),
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k A)))).map i ≫ φ₁ =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k A)))).map i ≫ φ₂ →
      φ₁ = φ₂ at h
  rw [hb] at h
  exact h

end Langlands.GroupScheme
