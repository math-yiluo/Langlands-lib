import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Transport of point Weyl quotients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- The all-test torus normalizer commutes with arbitrary base change. -/
theorem torusNormalizer_baseChange (b : S' ⟶ S) (i : T.toGrp ⟶ G) :
    torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) = (torusNormalizer i).baseChange b := by
  unfold torusNormalizer
  rw [SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.normalizer_baseChange]

/-- Normalizer membership is transported by the pullback point equivalence. -/
theorem mem_torusNormalizer_baseChange_iff (b : S' ⟶ S) (i : T.toGrp ⟶ G)
    (U : Over S') (x : U ⟶ ((GroupScheme.baseChange b).obj G).X) :
    x ∈ (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i)).carrier U ↔
      baseChangePointsEquiv b G U x ∈ (torusNormalizer i).carrier ((Over.map b).obj U) := by
  rw [torusNormalizer_baseChange]
  rfl

/-- The pullback point equivalence restricts to the actual torus normalizers. -/
def torusNormalizerBaseChangeEquiv (b : S' ⟶ S) (i : T.toGrp ⟶ G) (U : Over S') :
    (torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i)).carrier U ≃*
      (torusNormalizer i).carrier ((Over.map b).obj U) where
  toFun x := ⟨baseChangePointsEquiv b G U x,
    (mem_torusNormalizer_baseChange_iff b i U x).mp x.property⟩
  invFun x := ⟨(baseChangePointsEquiv b G U).symm x,
    (mem_torusNormalizer_baseChange_iff b i U _).mpr (by
      simpa only [MulEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext ((baseChangePointsEquiv b G U).left_inv x)
  right_inv x := Subtype.ext ((baseChangePointsEquiv b G U).right_inv x)
  map_mul' x y := Subtype.ext ((baseChangePointsEquiv b G U).map_mul x y)

/-- Base change identifies the point Weyl quotient on every test scheme. -/
def pointWeylGroupBaseChangeEquiv (b : S' ⟶ S) (i : T.toGrp ⟶ G) (U : Over S') :
    pointWeylGroup (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) U ≃*
      pointWeylGroup i ((Over.map b).obj U) :=
  QuotientGroup.congr
    (((torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i)).carrier U).subgroupOf
        ((torusNormalizer (T := (CommGroupScheme.baseChange b).obj T)
          ((GroupScheme.baseChange b).map i)).carrier U))
    (((torusCentralizer i).carrier ((Over.map b).obj U)).subgroupOf
      ((torusNormalizer i).carrier ((Over.map b).obj U)))
    (torusNormalizerBaseChangeEquiv b i U) (by
    rw [Subgroup.map_equiv_eq_comap_symm]
    ext x
    change ((torusNormalizerBaseChangeEquiv b i U).symm x).val ∈
      (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i)).carrier U ↔
      x.val ∈ (torusCentralizer i).carrier ((Over.map b).obj U)
    rw [torusCentralizer_baseChange, SubgroupFunctor.mem_baseChange]
    change baseChangePointsEquiv b G U ((baseChangePointsEquiv b G U).symm x.val) ∈
      (torusCentralizer i).carrier ((Over.map b).obj U) ↔ _
    rw [MulEquiv.apply_symm_apply])

section SourceIso

variable {T' : CommGroupScheme S}

/-- An isomorphism of the source leaves the all-test normalizer unchanged. -/
theorem torusNormalizer_iso_comp (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G) :
    torusNormalizer (T := T') (e.hom ≫ i) = torusNormalizer i := by
  unfold torusNormalizer
  rw [SubgroupFunctor.range_iso_comp]

/-- An isomorphism of the source leaves the all-test centralizer unchanged. -/
theorem torusCentralizer_iso_comp (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G) :
    torusCentralizer (T := T') (e.hom ≫ i) = torusCentralizer i := by
  rw [torusCentralizer_eq_centralizer_range, torusCentralizer_eq_centralizer_range,
    SubgroupFunctor.range_iso_comp]

/-- The point Weyl quotient is unchanged by an isomorphism of the torus source. -/
def pointWeylGroupSourceIsoEquiv (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G)
    (U : Over S) : pointWeylGroup (T := T') (e.hom ≫ i) U ≃* pointWeylGroup i U :=
  QuotientGroup.congr
    (((torusCentralizer (T := T') (e.hom ≫ i)).carrier U).subgroupOf
      ((torusNormalizer (T := T') (e.hom ≫ i)).carrier U))
    (((torusCentralizer i).carrier U).subgroupOf ((torusNormalizer i).carrier U))
    (MulEquiv.subgroupCongr (congrArg (fun F => F.carrier U)
      (torusNormalizer_iso_comp e i))) (by
        rw [Subgroup.map_equiv_eq_comap_symm]
        ext x
        change x.val ∈ (torusCentralizer (T := T') (e.hom ≫ i)).carrier U ↔
          x.val ∈ (torusCentralizer i).carrier U
        rw [torusCentralizer_iso_comp])

end SourceIso

section Field

variable {k : Type u} [Field k]
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational Weyl quotient is the point Weyl quotient on the base test scheme. -/
def relativeWeylGroupPointEquiv (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] :
    relativeWeylGroup i ≃* pointWeylGroup i (Over.mk (𝟙 _)) :=
  QuotientGroup.congr
    ((centralizerPoints i).subgroupOf (normalizerPoints i))
    (((torusCentralizer i).carrier (Over.mk (𝟙 _))).subgroupOf
      ((torusNormalizer i).carrier (Over.mk (𝟙 _))))
    (MulEquiv.subgroupCongr (torusNormalizer_carrier_base i).symm) (by
      rw [Subgroup.map_equiv_eq_comap_symm]
      ext x
      change x.val ∈ centralizerPoints i ↔
        x.val ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _))
      rw [torusCentralizer_carrier_base])

end Field

/-- On a field-valued fibre with a monomorphic torus map, the rational Weyl quotient is
the original point quotient on that field-valued test scheme. -/
def fibreRelativeWeylGroupEquiv {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) (i : T.toGrp ⟶ G)
    [Mono ((GroupScheme.baseChange b).map i).hom.hom.left] :
    relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map i) ≃* pointWeylGroup i (Over.mk b) := by
  let e := (relativeWeylGroupPointEquiv (T := (CommGroupScheme.baseChange b).obj T)
    ((GroupScheme.baseChange b).map i)).trans
      (pointWeylGroupBaseChangeEquiv b i (Over.mk (𝟙 _)))
  change relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj T)
    ((GroupScheme.baseChange b).map i) ≃*
      pointWeylGroup i (Over.mk ((𝟙 _) ≫ b)) at e
  exact Eq.mp (congrArg (fun f : Spec (CommRingCat.of k) ⟶ S =>
    relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i) ≃* pointWeylGroup i (Over.mk f))
        (Category.id_comp b)) e

end Langlands.GroupScheme
