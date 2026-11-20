import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Rational.NumberFieldOrthogonalHasseReduction

/-! # Correction of a natural cocycle by a central kernel cocycle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

variable {S S' : Scheme.{u}} {G H K : GroupScheme S} {U : Over S} {f : G ⟶ H}

private theorem twist_mem_kernel (ξ : Cocycle G U) (x : U ⟶ G.X)
    (hx : ∀ {Z : Over S} (a b : Z ⟶ U),
      (ξ.map f).toFun a b = (a ≫ x ≫ f.hom.hom) * (b ≫ x ≫ f.hom.hom)⁻¹)
    {Z : Over S} (a b : Z ⟶ U) :
    ∃ k : Z ⟶ (kernel f).X, k ≫ (kernelι f).hom.hom = (ξ.twist x).toFun a b := by
  apply (mem_range_kernelι_iff f _).mpr
  change ((a ≫ x)⁻¹ * ξ.toFun a b * (b ≫ x)) ≫ f.hom.hom = 1
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  rw [show ξ.toFun a b ≫ f.hom.hom = _ from hx a b]
  group

/-- A cochain lifting the projected coboundary makes the twisted cocycle kernel-valued. -/
def kernelCorrection (ξ : Cocycle G U) (x : U ⟶ G.X)
    (hx : ∀ {Z : Over S} (a b : Z ⟶ U),
      (ξ.map f).toFun a b = (a ≫ x ≫ f.hom.hom) * (b ≫ x ≫ f.hom.hom)⁻¹) :
    Cocycle (kernel f) U :=
  (ξ.twist x).lift (kernelι f) (twist_mem_kernel ξ x hx)

/-- The correction maps to the original cocycle twisted by the lifting cochain. -/
theorem kernelCorrection_cohomologous (ξ : Cocycle G U) (x : U ⟶ G.X)
    (hx : ∀ {Z : Over S} (a b : Z ⟶ U),
      (ξ.map f).toFun a b = (a ≫ x ≫ f.hom.hom) * (b ≫ x ≫ f.hom.hom)⁻¹) :
    ξ.Cohomologous ((ξ.kernelCorrection x hx).map (kernelι f)) :=
  ⟨x, fun a b => (ξ.twist x).lift_toFun (kernelι f) (twist_mem_kernel ξ x hx) a b⟩

/-- Subtract a central cocycle from another cocycle by multiplying by its pointwise inverse. -/
def divCentral (ξ : Cocycle G U) (α : Cocycle K U) (j : K ⟶ G) (hj : IsCentral j) :
    Cocycle G U where
  toFun a b := ξ.toFun a b * (α.toFun a b ≫ j.hom.hom)⁻¹
  naturality t a b := by
    simp only [ξ.naturality, α.naturality, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  cocycle a b c := by
    rw [ξ.cocycle a b c, α.cocycle a b c, MonObj.mul_comp, mul_inv_rev]
    have h := (commute_of_mem_center (hj _ (α.toFun a b))
      (ξ.toFun b c * (α.toFun b c ≫ j.hom.hom)⁻¹)).inv_left.eq
    simp only [mul_assoc]
    rw [← mul_assoc (ξ.toFun b c), ← h]

/-- Cohomologous central corrections make the difference a coboundary. -/
theorem isTrivial_divCentral (ξ : Cocycle G U) (α : Cocycle K U) (j : K ⟶ G) (hj : IsCentral j)
    (h : ξ.Cohomologous (α.map j)) : (ξ.divCentral α j hj).IsTrivial := by
  obtain ⟨g, hg⟩ := h.symm
  refine ⟨g⁻¹, fun a b => ?_⟩
  change ξ.toFun a b * (α.toFun a b ≫ j.hom.hom)⁻¹ = (a ≫ g⁻¹) * (b ≫ g⁻¹)⁻¹
  rw [hg]
  simp only [twist, map, GrpObj.comp_inv, inv_inv]
  have hc := (commute_of_mem_center (hj _ (α.toFun a b)) (b ≫ g)).eq
  rw [mul_assoc ((a ≫ g)⁻¹), hc]
  group

/-- A correction in the actual kernel leaves the projected values unchanged. -/
theorem divCentral_kernel_map_toFun (ξ : Cocycle G U) (α : Cocycle (kernel f) U)
    (hj : IsCentral (kernelι f)) {Z : Over S} (a b : Z ⟶ U) :
    ((ξ.divCentral α (kernelι f) hj).map f).toFun a b = (ξ.map f).toFun a b := by
  have hk : (α.toFun a b ≫ (kernelι f).hom.hom) ≫ f.hom.hom = 1 :=
    (kernelPointsEquiv f Z (α.toFun a b)).property
  change (ξ.toFun a b * (α.toFun a b ≫ (kernelι f).hom.hom)⁻¹) ≫ f.hom.hom = _
  rw [MonObj.mul_comp, GrpObj.inv_comp, hk, inv_one, mul_one]
  rfl

/-- The base change of a centrally corrected cocycle has the corresponding corrected values. -/
theorem baseChange_divCentral_toFun (ξ : Cocycle G U) (α : Cocycle K U)
    (j : K ⟶ G) (hj : IsCentral j) (b : S' ⟶ S) (V : Over S') (r : (Over.map b).obj V ⟶ U)
    {Z : Over S'} (a c : Z ⟶ V) :
    ((ξ.divCentral α j hj).baseChange b V r).toFun a c =
      ((ξ.baseChange b V r).divCentral (α.baseChange b V r) ((GroupScheme.baseChange b).map j)
        (hj.baseChange b)).toFun a c := by
  apply (baseChangePointsEquiv b G Z).injective
  rw [baseChange_toFun]
  change _ = baseChangePointsEquiv b G Z ((ξ.baseChange b V r).toFun a c *
    (((α.baseChange b V r).map ((GroupScheme.baseChange b).map j)).toFun a c)⁻¹)
  rw [map_mul, map_inv, baseChange_toFun, ← baseChange_map_toFun, baseChange_toFun]
  rfl

end Langlands.GroupScheme.Cocycle
