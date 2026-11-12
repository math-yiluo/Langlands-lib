import Langlands.GroupScheme.GaloisPointRational

/-! # Rational sections under an isomorphism of base schemes -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Changing a section's base along an isomorphism is bijective. -/
theorem baseChangeSectionHom_bijective_of_isIso {S T : Scheme.{u}}
    (b : T ⟶ S) [IsIso b] (G : GroupScheme S) :
    Function.Bijective (baseChangeSectionHom b G) := by
  let q : Over.mk b ≅ Over.mk (𝟙 S) := Over.isoMk (asIso b)
  have h : Function.Bijective
      ((G.points.map (Over.homMk b (by simp) :
        Over.mk b ⟶ Over.mk (𝟙 S)).op).hom) := by
    exact (G.points.mapIso q.op).groupIsoToMulEquiv.bijective
  exact (baseChangeBasePointsEquiv b G).symm.bijective.comp h

namespace GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Rational extension is the existing section base-change homomorphism. -/
theorem rationalExtend_hom_eq_baseChangeSectionHom :
    rationalExtend k K G = baseChangeSectionHom (baseMap k K) G := by
  ext x
  apply pullback.hom_ext
  · rw [rationalExtend_fst, baseChangeSectionHom_fst]
  · exact (rationalExtend k K G x).w.trans
      (baseChangeSectionHom (baseMap k K) G x).w.symm

/-- A bijective map of fields induces a bijection on rational sections. -/
theorem rationalExtend_bijective_of_bijective
    (h : Function.Bijective (algebraMap k K)) :
    Function.Bijective (rationalExtend k K G) := by
  have : IsIso (baseMap k K) := isIso_SpecMap_iff.mpr h
  rw [rationalExtend_hom_eq_baseChangeSectionHom]
  exact baseChangeSectionHom_bijective_of_isIso _ _

end GaloisPointComparison

end Langlands.GroupScheme
