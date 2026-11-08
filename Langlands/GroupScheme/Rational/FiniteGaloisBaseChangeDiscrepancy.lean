import Langlands.GroupScheme.Adjoint.LocalIsomorphism
import Langlands.GroupScheme.AutomorphicActionPointIso
import Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy

/-! # Finite Galois discrepancies of base-change isomorphisms through base-changed inner actions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

section General

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

@[reassoc] private theorem baseChange_map_fst {T : Scheme.{u}} (f : T ⟶ S)
    {G H : GroupScheme S} (a : G ⟶ H) :
    ((baseChange f).map a).hom.hom.left ≫ pullback.fst H.X.hom f =
      pullback.fst G.X.hom f ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The lifted point has the original point as its first pullback coordinate. -/
theorem coverPointsEquiv_symm_left_fst (G : GroupScheme S) {T : Over S} (a : T ⟶ U)
    (g : T ⟶ G.X) :
    ((coverPointsEquiv G a).symm g).left ≫ pullback.fst G.X.hom U.hom = g.left := by
  have h := coverPointsEquiv_left G a ((coverPointsEquiv G a).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- The lifted point has the cover point as its second pullback coordinate. -/
theorem coverPointsEquiv_symm_left_snd (G : GroupScheme S) {T : Over S} (a : T ⟶ U)
    (g : T ⟶ G.X) :
    ((coverPointsEquiv G a).symm g).left ≫ pullback.snd G.X.hom U.hom = a.left :=
  Over.w ((coverPointsEquiv G a).symm g)

/-- Precomposing the cover point with an endomorphism of the cover pulls the
base-change isomorphism back along that endomorphism. -/
theorem ofBaseChangeIso_comp_cover
    (E : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H)
    (r : U ⟶ U) {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (ofBaseChangeIso E).toFun (a ≫ r) g =
      (ofBaseChangeIso (Descent.pullIso r.left (Over.w r) (Over.w r) E)).toFun a g := by
  apply Over.OverMorphism.ext
  rw [ofBaseChangeIso_toFun_left, ofBaseChangeIso_toFun_left]
  have hc : pullback.fst ((baseChange U.hom).obj G).X.hom r.left ≫
      pullback.snd G.X.hom U.hom =
      pullback.snd ((baseChange U.hom).obj G).X.hom r.left ≫ r.left :=
    pullback.condition
  have hw : (Descent.pullbackComparison U.hom r.left U.hom (Over.w r) G).inv.hom.hom.left ≫
      pullback.snd ((baseChange U.hom).obj G).X.hom r.left =
      pullback.snd G.X.hom U.hom :=
    Over.w (Descent.pullbackComparison U.hom r.left U.hom (Over.w r) G).inv.hom.hom
  have key : ((coverPointsEquiv G a).symm g).left ≫
      (Descent.pullbackComparison U.hom r.left U.hom (Over.w r) G).inv.hom.hom.left ≫
        pullback.fst ((baseChange U.hom).obj G).X.hom r.left =
      ((coverPointsEquiv G (a ≫ r)).symm g).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Descent.pullbackComparison_inv_fst,
        coverPointsEquiv_symm_left_fst]
    · rw [coverPointsEquiv_symm_left_snd, Category.assoc, Category.assoc, hc,
        ← Category.assoc _ (pullback.snd _ _) r.left, hw, ← Category.assoc,
        coverPointsEquiv_symm_left_snd]
      rfl
  rw [← key]
  simp only [Descent.pullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_hom_fst, baseChange_map_fst_assoc]

/-- The point of `A` over the cover determined by a base point of the base change of `A`
to the cover. -/
def coverBasePoint (A : GroupScheme S)
    (x : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj A).X) : U ⟶ A.X :=
  coverPointsEquiv A (𝟙 U) x

@[simp] theorem coverBasePoint_left (A : GroupScheme S)
    (x : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj A).X) :
    (coverBasePoint A x).left = x.left ≫ pullback.fst A.X.hom U.hom :=
  coverPointsEquiv_left A (𝟙 U) x

end General

end LocalGroupIso

namespace IsAdjointQuotient

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- The inner action of the base-changed adjoint quotient is the base change of the
original inner action on every relative test scheme. -/
theorem baseChangePointsEquiv_innerAction {T : Over (Spec (CommRingCat.of K))}
    (z : T ⟶ ((baseChange (algebraBaseMap k K)).obj A).X)
    (y : T ⟶ ((baseChange (algebraBaseMap k K)).obj G).X) :
    baseChangePointsEquiv (algebraBaseMap k K) G T
        ((adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq).innerAction.act
          z y) =
      hq.innerAction.act (baseChangePointsEquiv (algebraBaseMap k K) A T z)
        (baseChangePointsEquiv (algebraBaseMap k K) G T y) := by
  have hqK := adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq
  let := hqK.flat
  let := hqK.surjective
  let := hqK.isConnectedReductive.isAffineHom
  let := hqK.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine ((baseChange (algebraBaseMap k K)).obj G).X.left :=
    isAffine_of_isAffineHom ((baseChange (algebraBaseMap k K)).obj G).X.hom
  let : IsAffine ((baseChange (algebraBaseMap k K)).obj A).X.left :=
    isAffine_of_isAffineHom ((baseChange (algebraBaseMap k K)).obj A).X.hom
  apply (baseChangePointsEquiv (algebraBaseMap k K) G T).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply AutomorphicAction.hom_ext_of_local_quotient_lift
    ((baseChange (algebraBaseMap k K)).map q) z
  intro V c h hc
  rw [AutomorphicAction.naturality, hc, IsAdjointQuotient.innerAction_act_lift]
  apply (baseChangePointsEquiv (algebraBaseMap k K) G V).injective
  rw [baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply,
    AutomorphicAction.naturality, ← baseChangePointsEquiv_naturality,
    ← baseChangePointsEquiv_naturality, hc, baseChangePointsEquiv_comp,
    hq.innerAction_act_lift, map_mul, map_mul, map_inv]

/-- The inner action of the base-changed adjoint quotient is the original inner action
after projecting points from the cover. -/
theorem coverPointsEquiv_innerAction {T : Over (Spec (CommRingCat.of k))}
    (a : T ⟶ ringTest k K)
    (z : LocalGroupIso.coverTest a ⟶ ((baseChange (algebraBaseMap k K)).obj A).X)
    (y : LocalGroupIso.coverTest a ⟶ ((baseChange (algebraBaseMap k K)).obj G).X) :
    LocalGroupIso.coverPointsEquiv G a
        ((adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq).innerAction.act
          z y) =
      hq.innerAction.act (LocalGroupIso.coverPointsEquiv A a z)
        (LocalGroupIso.coverPointsEquiv G a y) := by
  change (LocalGroupIso.coverTestIso a).inv ≫ baseChangePointsEquiv (algebraBaseMap k K) G
      (LocalGroupIso.coverTest a) _ =
    hq.innerAction.act ((LocalGroupIso.coverTestIso a).inv ≫
        baseChangePointsEquiv (algebraBaseMap k K) A (LocalGroupIso.coverTest a) z)
      ((LocalGroupIso.coverTestIso a).inv ≫
        baseChangePointsEquiv (algebraBaseMap k K) G (LocalGroupIso.coverTest a) y)
  rw [baseChangePointsEquiv_innerAction, AutomorphicAction.naturality]

/-- Projecting the constant family of a base point of the base-changed adjoint quotient
to a point of the cover gives the cover point precomposed with the test point. -/
theorem coverPointsEquiv_constantPoint {T : Over (Spec (CommRingCat.of k))}
    (a : T ⟶ ringTest k K)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((baseChange (algebraBaseMap k K)).obj A).X) :
    LocalGroupIso.coverPointsEquiv A a
        (((baseChange (algebraBaseMap k K)).obj A).constantPoint x
          (LocalGroupIso.coverTest a)) =
      a ≫ LocalGroupIso.coverBasePoint A x := by
  apply Over.OverMorphism.ext
  rw [LocalGroupIso.coverPointsEquiv_left, Over.comp_left, LocalGroupIso.coverBasePoint_left]
  exact Category.assoc a.left x.left _

/-- Precomposing a base-change isomorphism with an inner automorphism of the base-changed
group, given by a base point of the base-changed adjoint quotient, inserts the original
inner action at the corresponding cover point. -/
theorem ofBaseChangeIso_basePointIso_trans {H : GroupScheme (Spec (CommRingCat.of k))}
    (E : (baseChange (ringTest k K).hom).obj G ≅ (baseChange (ringTest k K).hom).obj H)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((baseChange (algebraBaseMap k K)).obj A).X)
    {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ ringTest k K) (g : T ⟶ G.X) :
    (LocalGroupIso.ofBaseChangeIso
        ((adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K)
          hq).innerAction.basePointIso x ≪≫ E)).toFun a g =
      (LocalGroupIso.ofBaseChangeIso E).toFun a
        (hq.innerAction.act (a ≫ LocalGroupIso.coverBasePoint A x) g) := by
  change LocalGroupIso.coverPointsEquiv H a
      ((LocalGroupIso.coverPointsEquiv G a).symm g ≫
        ((adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K)
          hq).innerAction.basePointIso x ≪≫ E).hom.hom.hom) =
    LocalGroupIso.coverPointsEquiv H a
      ((LocalGroupIso.coverPointsEquiv G a).symm
          (hq.innerAction.act (a ≫ LocalGroupIso.coverBasePoint A x) g) ≫
        E.hom.hom.hom)
  congr 1
  rw [Iso.trans_hom, Grp.comp_hom_hom, ← Category.assoc,
    AutomorphicAction.comp_basePointIso_hom]
  congr 1
  apply (LocalGroupIso.coverPointsEquiv G a).injective
  rw [MulEquiv.apply_symm_apply, coverPointsEquiv_innerAction, coverPointsEquiv_constantPoint,
    MulEquiv.apply_symm_apply]

variable [FiniteDimensional k K] [IsGalois k K]

/-- If every Galois pullback of a base-change isomorphism differs from it by an inner
automorphism coming from a base point of the base-changed adjoint quotient, then the
induced local isomorphism has all-test inner discrepancy. -/
theorem hasInnerDiscrepancy_of_galois_baseChange {H : GroupScheme (Spec (CommRingCat.of k))}
    (E : (baseChange (ringTest k K).hom).obj G ≅ (baseChange (ringTest k K).hom).obj H)
    (h : ∀ σ : K ≃ₐ[k] K, ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        ((baseChange (algebraBaseMap k K)).obj A).X,
      (adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K)
          hq).innerAction.basePointIso x ≪≫ E =
        Descent.pullIso (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
          (galoisBaseMap_over k K σ) E) :
    (LocalGroupIso.ofBaseChangeIso E).HasInnerDiscrepancy hq.innerAction := by
  choose x hx using h
  apply LocalGroupIso.hasInnerDiscrepancy_of_galois _ _
    (fun σ => LocalGroupIso.coverBasePoint A (x σ))
  intro σ V s g
  rw [← ofBaseChangeIso_basePointIso_trans, hx σ,
    LocalGroupIso.ofBaseChangeIso_comp_cover]
  rfl

end IsAdjointQuotient

end Langlands.GroupScheme
