import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.LocalGroupIso

/-! # Comparing cocycles by inner twisting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S S' : Scheme.{u}} {G H Q : GroupScheme S} {U : Over S}
    (ξ ζ : Cocycle G U) (e : LocalGroupIso G H U)
    (he : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ζ)

include he in
private theorem innerDiscrepancy {Z : Over S} (a b : Z ⟶ U) (g : Z ⟶ G.X) :
    e.toFun a (ζ.toFun a b * g * (ζ.toFun a b)⁻¹) = e.toFun b g := by
  simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
    using he a b g

/-- The difference from `ζ`, in the group obtained by descent through conjugation
by `ζ`. Its formula uses the local identification at the first cover point. -/
def innerDifference : Cocycle H U where
  toFun a b := e.toFun a (ξ.toFun a b * (ζ.toFun a b)⁻¹)
  naturality t a b := by
    rw [ξ.naturality, ζ.naturality, ← GrpObj.comp_inv, ← MonObj.comp_mul, e.naturality]
  cocycle a b c := by
    rw [← innerDiscrepancy ζ e he a b (ξ.toFun b c * (ζ.toFun b c)⁻¹), ← map_mul]
    apply congrArg (e.toFun a)
    rw [ξ.cocycle a b c, ζ.cocycle a b c]
    group

theorem innerDifference_toFun {Z : Over S} (a b : Z ⟶ U) :
    (innerDifference ξ ζ e he).toFun a b = e.toFun a (ξ.toFun a b * (ζ.toFun a b)⁻¹) :=
  rfl

private theorem innerDifference_eq_iff {Z : Over S} (a b : Z ⟶ U) (x y : Z ⟶ G.X) :
    (innerDifference ξ ζ e he).toFun a b = e.toFun a x * (e.toFun b y)⁻¹ ↔
      ζ.toFun a b = x⁻¹ * ξ.toFun a b * y := by
  rw [innerDifference_toFun, ← innerDiscrepancy ζ e he a b y, ← map_inv, ← map_mul,
    (e.toFun a).injective.eq_iff]
  constructor
  · intro h
    calc
      ζ.toFun a b =
          x⁻¹ * (x * (ζ.toFun a b * y * (ζ.toFun a b)⁻¹)⁻¹) * ζ.toFun a b * y := by group
      _ = _ := by rw [← h]; group
  · intro h
    have hξ : ξ.toFun a b = x * ζ.toFun a b * y⁻¹ := by
      rw [h]
      group
    rw [hξ]
    group

/-- Triviality of the difference in the twisted group is equivalent to cohomology
of the original two cocycles on the same cover. -/
theorem isTrivial_innerDifference_iff :
    (innerDifference ξ ζ e he).IsTrivial ↔ ξ.Cohomologous ζ := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, rfl⟩ := (e.toFun (𝟙 U)).surjective f
    refine ⟨g, fun a b => (innerDifference_eq_iff ξ ζ e he a b _ _).mp ?_⟩
    simpa only [← e.naturality, Category.comp_id] using hf a b
  · rintro ⟨g, hg⟩
    refine ⟨e.toFun (𝟙 U) g, fun a b => ?_⟩
    simpa only [← e.naturality, Category.comp_id] using
      (innerDifference_eq_iff ξ ζ e he a b (a ≫ g) (b ≫ g)).mpr (hg a b)

/-- A twist cochain after base change gives a trivializing cochain for the
base-changed difference, on the same compatible cover. -/
theorem isTrivial_innerDifference_baseChange (p : S' ⟶ S) (V : Over S')
    (r : (Over.map p).obj V ⟶ U)
    (h : (ξ.baseChange p V r).Cohomologous (ζ.baseChange p V r)) :
    ((innerDifference ξ ζ e he).baseChange p V r).IsTrivial := by
  obtain ⟨f, hf⟩ := h
  let g := baseChangePointsEquiv p G V f
  let v := (baseChangePointsEquiv p H V).symm (e.toFun r g)
  refine ⟨v, fun {Z} a b => ?_⟩
  apply (baseChangePointsEquiv p H Z).injective
  rw [baseChange_toFun, map_mul, map_inv,
    baseChangePointsEquiv_naturality, baseChangePointsEquiv_naturality]
  simp only [v, MulEquiv.apply_symm_apply, ← e.naturality]
  apply (innerDifference_eq_iff ξ ζ e he _ _ _ _).mpr
  have hpoint := congrArg (baseChangePointsEquiv p G Z) (hf a b)
  simpa only [twist, baseChange_toFun, map_mul, map_inv, baseChangePointsEquiv_naturality,
    g] using hpoint

/-- A homomorphism which agrees under the local identifications sends the inner
difference to the pointwise difference of the two original images. -/
theorem map_innerDifference_toFun (q : G ⟶ Q) (r : H ⟶ Q)
    (h : ∀ {Z : Over S} (a : Z ⟶ U) (g : Z ⟶ G.X),
      e.toFun a g ≫ r.hom.hom = g ≫ q.hom.hom)
    {Z : Over S} (a b : Z ⟶ U) :
    ((innerDifference ξ ζ e he).map r).toFun a b =
      (ξ.map q).toFun a b * ((ζ.map q).toFun a b)⁻¹ := by
  change e.toFun a (ξ.toFun a b * (ζ.toFun a b)⁻¹) ≫ r.hom.hom = _
  rw [h, MonObj.mul_comp, GrpObj.inv_comp]
  rfl

end Langlands.GroupScheme.Cocycle
