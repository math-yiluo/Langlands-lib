import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityDescent
import Langlands.AbelianScheme.KernelBaseChange

/-! # Torus conjugation under arbitrary base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}

/-- Projection of actual pullback points identifies torus conjugation over a
new base with torus conjugation on the same parameter scheme over the old base. -/
theorem torusConjugates_baseChange_iff
    (b : S' ⟶ S) (i : T.toGrp ⟶ H) (f F : G ⟶ H) (V : Over S')
    (t : V ⟶ ((CommGroupScheme.baseChange b).obj T).X) :
    TorusConjugates ((GroupScheme.baseChange b).map i)
        ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map F) t ↔
      TorusConjugates i f F (baseChangePointsEquiv b T.toGrp V t) := by
  constructor
  · intro ht U a g
    let W : Over S' := Over.mk (a.left ≫ V.hom)
    let c : W ⟶ V := Over.homMk a.left rfl
    let e : (Over.map b).obj W ≅ U :=
      Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ U.hom = (a.left ≫ V.hom) ≫ b
        have ha : a.left ≫ (V.hom ≫ b) = U.hom := Over.w a
        simpa only [Category.id_comp, Category.assoc] using ha.symm)
    have hc : (Over.map b).map c = e.hom ≫ a := by
      apply Over.OverMorphism.ext
      exact (Category.id_comp a.left).symm
    let x := (baseChangePointsEquiv b G W).symm (e.hom ≫ g)
    have h₀ := ht W c x
    simp only [← Category.assoc] at h₀
    have h := congrArg (baseChangePointsEquiv b H W) h₀
    simp only [map_mul, map_inv, baseChangePointsEquiv_comp] at h
    simp only [baseChangePointsEquiv_naturality, x, MulEquiv.apply_symm_apply] at h
    rw [hc] at h
    apply (cancel_epi e.hom).mp
    simpa only [Category.assoc, MonObj.comp_mul, GrpObj.comp_inv] using h
  · intro ht U a g
    simp only [← Category.assoc]
    apply (baseChangePointsEquiv b H U).injective
    simp only [map_mul, map_inv, baseChangePointsEquiv_comp]
    simp only [baseChangePointsEquiv_naturality]
    exact ht ((Over.map b).obj U) ((Over.map b).map a)
      (baseChangePointsEquiv b G U g)

/-- The pullback-point equivalence restricts to the points conjugating two
specified group-scheme homomorphisms by the supplied commutative group. -/
def torusConjugatorPointsEquiv (b : S' ⟶ S) (i : T.toGrp ⟶ H)
    (f F : G ⟶ H) (V : Over S') :
    {t : V ⟶ ((CommGroupScheme.baseChange b).obj T).X //
      TorusConjugates ((GroupScheme.baseChange b).map i)
        ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map F) t} ≃
    {t : (Over.map b).obj V ⟶ T.X // TorusConjugates i f F t} where
  toFun t := ⟨baseChangePointsEquiv b T.toGrp V t.1,
    (torusConjugates_baseChange_iff b i f F V t.1).mp t.2⟩
  invFun t := ⟨(baseChangePointsEquiv b T.toGrp V).symm t.1,
    (torusConjugates_baseChange_iff b i f F V _).mpr (by
      simpa only [MulEquiv.apply_symm_apply] using t.2)⟩
  left_inv t := Subtype.ext ((baseChangePointsEquiv b T.toGrp V).symm_apply_apply t.1)
  right_inv t := Subtype.ext ((baseChangePointsEquiv b T.toGrp V).apply_symm_apply t.1)

/-- Changing the supplied commutative group by an isomorphism preserves the
all-test conjugation predicate, with the point sent through that isomorphism. -/
theorem torusConjugates_torusIso_iff {U : CommGroupScheme S}
    (e : U.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ H) (f F : G ⟶ H)
    {V : Over S} (t : V ⟶ U.X) :
    TorusConjugates (e.hom ≫ i) f F t ↔
      TorusConjugates i f F (t ≫ e.hom.hom.hom) := by
  simp only [TorusConjugates, Grp.comp_hom_hom, Category.assoc]

end Langlands.GroupScheme
