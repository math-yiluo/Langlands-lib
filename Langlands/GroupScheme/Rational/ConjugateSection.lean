import Langlands.GroupScheme.Rational.NormalizerGaloisAction

/-! # Coefficient conjugation of changed sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GaloisPointComparison

/-- The section homomorphism and pullback of a base point are the same map. -/
theorem baseChangeSectionHom_eq_baseChangeBasePoint
    {S S' : Scheme.{u}} (b : S' ⟶ S) (H : GroupScheme S)
    (x : Over.mk (𝟙 S) ⟶ H.X) :
    baseChangeSectionHom b H x = baseChangeBasePoint b H x := by
  apply Over.OverMorphism.ext
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [baseChangeSectionHom_fst, baseChangeBasePoint_fst]
  · exact (baseChangeSectionHom b H x).w.trans (baseChangeBasePoint b H x).w.symm

/-- Pullback of a section followed by the composite changed morphism agrees with
changing the image section. -/
theorem baseChangeSectionHom_comp_map
    {S S' : Scheme.{u}} (b : S' ⟶ S)
    {H J : GroupScheme S} {Q : GroupScheme S'}
    (i : H ⟶ J) (j : (GroupScheme.baseChange b).obj J ⟶ Q)
    (t : Over.mk (𝟙 S) ⟶ H.X) :
    baseChangeSectionHom b J (t ≫ i.hom.hom) ≫ j.hom.hom =
      baseChangeSectionHom b H t ≫ ((GroupScheme.baseChange b).map i ≫ j).hom.hom := by
  rw [baseChangeSectionHom_naturality]
  exact Category.assoc _ _ _

/-- Projection of the changed image section after canonical ambient descent. -/
theorem baseChangeSectionHom_comp_descent_fst
    {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    (G : GroupScheme B) {H : GroupScheme S}
    (i : H ⟶ (GroupScheme.baseChange b).obj G)
    (t : Over.mk (𝟙 S) ⟶ H.X) :
    (baseChangeSectionHom a H t ≫
      ((GroupScheme.baseChange a).map i ≫ (descentBaseChangeIso b a ha G).hom).hom.hom).left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom b =
      a ≫ (t ≫ i.hom.hom).left ≫ CategoryTheory.Limits.pullback.fst G.X.hom b := by
  rw [← baseChangeSectionHom_comp_map]
  rw [Over.comp_left, Category.assoc, descentBaseChangeIso_hom_fst,
    ← Category.assoc]
  exact (congrArg (fun z => z ≫ CategoryTheory.Limits.pullback.fst G.X.hom b)
    (baseChangeSectionHom_fst a ((GroupScheme.baseChange b).obj G)
      (t ≫ i.hom.hom))).trans (Category.assoc _ _ _)


/-- The projection to the original scheme determines an actual conjugate point. -/
theorem rationalConjugate_eq_of_fst
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (σ : K ≃ₐ[k] K)
    (n m : rationalPoints (baseChanged k K G))
    (hm : m.left ≫ CategoryTheory.Limits.pullback.fst G.X.hom (baseMap k K) =
      galoisBaseMap k K σ ≫ n.left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (baseMap k K)) :
    rationalConjugate k K G σ n = m := by
  apply (baseChangeCoeffEquiv k K G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_rationalConjugate, baseChangeCoeffEquiv_left]
  change galoisBaseMap k K σ ≫ (baseChangeCoeffEquiv k K G n).left = _
  rw [baseChangeCoeffEquiv_left]
  exact hm.symm

/-- Naturality of actual coefficient conjugation for an upstairs homomorphism. -/
theorem rationalConjugate_map_eq_baseChange_descent
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ baseChanged k K G) (σ : K ≃ₐ[k] K) (t : rationalPoints H) :
    rationalConjugate k K G σ (rationalPoints.map i t) =
      rationalPoints.map ((GroupScheme.baseChange (galoisBaseMap k K σ)).map i ≫
        (descentBaseChangeIso (baseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G).hom)
        (baseChangeSectionHom (galoisBaseMap k K σ) H t) := by
  apply rationalConjugate_eq_of_fst k K G σ
  rw [rationalPoints.map_apply, rationalPoints.map_apply]
  exact baseChangeSectionHom_comp_descent_fst (baseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G i t

/-- The generic comparison between coefficient conjugation and changed sections. -/
def ConjugateSectionNaturalityStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (H : GroupScheme (Spec (CommRingCat.of K)))
    (i : H ⟶ baseChanged k K G) (σ : K ≃ₐ[k] K) (t : rationalPoints H),
    rationalConjugate k K G σ (rationalPoints.map i t) =
      rationalPoints.map ((GroupScheme.baseChange (galoisBaseMap k K σ)).map i ≫
        (descentBaseChangeIso (baseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G).hom)
        (baseChangeSectionHom (galoisBaseMap k K σ) H t)

end Langlands.GroupScheme.GaloisPointComparison
