import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Moving a cocycle to the kernel using a lifted cochain -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S S' : Scheme.{u}} {G Q : GroupScheme S} {U : Over S}
    (ξ : Cocycle G U) (q : G ⟶ Q) (g : U ⟶ G.X)
    (hg : ∀ {Z : Over S} (a b : Z ⟶ U),
      (ξ.map q).toFun a b = (coboundary (g ≫ q.hom.hom)).toFun a b)

include hg in
private theorem twist_mem_kernel {Z : Over S} (a b : Z ⟶ U) :
    ∃ x : Z ⟶ (kernel q).X, x ≫ (kernelι q).hom.hom = (ξ.twist g).toFun a b := by
  apply SubgroupFunctor.mem_range.mp
  rw [mem_range_kernelι_iff]
  change ((a ≫ g)⁻¹ * ξ.toFun a b * (b ≫ g)) ≫ q.hom.hom = 1
  have h := hg a b
  change ξ.toFun a b ≫ q.hom.hom =
    (a ≫ g ≫ q.hom.hom) * (b ≫ g ≫ q.hom.hom)⁻¹ at h
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
    Category.assoc, h]
  group

/-- If the image of a cocycle is the coboundary of the image of `g`, the twist
by `g` has values in the actual kernel of the quotient homomorphism. -/
def kernelTwist : Cocycle (kernel q) U :=
  (ξ.twist g).lift (kernelι q) (twist_mem_kernel ξ q g hg)

/-- The kernel cocycle includes as the twist by the supplied cochain. -/
theorem kernelTwist_toFun_comp {Z : Over S} (a b : Z ⟶ U) :
    (kernelTwist ξ q g hg).toFun a b ≫ (kernelι q).hom.hom = (ξ.twist g).toFun a b :=
  lift_toFun (ξ.twist g) (kernelι q) (twist_mem_kernel ξ q g hg) a b

/-- A trivialization of the kernel cocycle gives one of the original cocycle. -/
theorem isTrivial_of_kernelTwist (h : (kernelTwist ξ q g hg).IsTrivial) : ξ.IsTrivial :=
  (IsTrivial.of_lift (hξ := twist_mem_kernel ξ q g hg) h).of_twist

/-- After base change to any compatible cover, a trivializing cochain for `ξ`
whose image agrees with that of `g` trivializes the associated kernel cocycle.
The comparison of the quotient images is written using the pullback adjunction. -/
theorem isTrivial_kernelTwist_baseChange (p : S' ⟶ S) (V : Over S')
    (r : (Over.map p).obj V ⟶ U) (f : V ⟶ ((GroupScheme.baseChange p).obj G).X)
    (hf : ∀ {Z : Over S'} (a b : Z ⟶ V),
      (ξ.baseChange p V r).toFun a b = (coboundary f).toFun a b)
    (hproj : baseChangePointsEquiv p Q V (f ≫ ((GroupScheme.baseChange p).map q).hom.hom) =
      r ≫ g ≫ q.hom.hom) :
    ((kernelTwist ξ q g hg).baseChange p V r).IsTrivial := by
  let w := baseChangePointsEquiv p G V f
  have hw : w ≫ q.hom.hom = r ≫ g ≫ q.hom.hom := by
    rw [← baseChangePointsEquiv_comp]
    exact hproj
  let d := (r ≫ g)⁻¹ * w
  have hd : d ≫ q.hom.hom = 1 := by
    change ((r ≫ g)⁻¹ * w) ≫ q.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hw, inv_mul_cancel]
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff q d).mpr hd)
  let v' := (baseChangePointsEquiv p (kernel q) V).symm v
  refine ⟨v', fun {Z} a b => ?_⟩
  apply (baseChangePointsEquiv p (kernel q) Z).injective
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [baseChange_toFun, kernelTwist_toFun_comp, map_mul, map_inv,
    baseChangePointsEquiv_naturality, baseChangePointsEquiv_naturality]
  simp only [v', MulEquiv.apply_symm_apply, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hv]
  have hab := congrArg (baseChangePointsEquiv p G Z) (hf a b)
  simp only [baseChange_toFun, coboundary, map_mul, map_inv,
    baseChangePointsEquiv_naturality] at hab
  simp only [twist, hab, d, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, w]
  group

end Langlands.GroupScheme.Cocycle
