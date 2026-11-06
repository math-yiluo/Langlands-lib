import Langlands.GroupScheme.Adjoint.Isomorphism
import Langlands.GroupScheme.Adjoint.BaseChangeProof
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence

/-! # Local isomorphisms induced on supplied adjoint quotients -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

section General
variable {S : Scheme.{u}} {G H A B : GroupScheme S} {U : Over S}

/-- Projection of pullback points at a cover point commutes with every group map. -/
theorem coverPointsEquiv_comp (q : G ⟶ A) {T : Over S} (a : T ⟶ U)
    (x : coverTest a ⟶ ((baseChange U.hom).obj G).X) :
    coverPointsEquiv A a (x ≫ ((baseChange U.hom).map q).hom.hom) =
      coverPointsEquiv G a x ≫ q.hom.hom := by
  change (coverTestIso a).inv ≫ baseChangePointsEquiv U.hom A (coverTest a)
      (x ≫ ((baseChange U.hom).map q).hom.hom) =
    ((coverTestIso a).inv ≫ baseChangePointsEquiv U.hom G (coverTest a) x) ≫ q.hom.hom
  rw [baseChangePointsEquiv_comp, Category.assoc]

/-- A square of actual base-change isomorphisms gives a square of local values
on every test scheme and every cover point. -/
theorem ofBaseChangeIso_square (q : G ⟶ A) (p : H ⟶ B)
    (e : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H)
    (d : (baseChange U.hom).obj A ≅ (baseChange U.hom).obj B)
    (hs : (baseChange U.hom).map q ≫ d.hom =
      e.hom ≫ (baseChange U.hom).map p)
    {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (ofBaseChangeIso d).toFun a (g ≫ q.hom.hom) =
      (ofBaseChangeIso e).toFun a g ≫ p.hom.hom := by
  let x := (coverPointsEquiv G a).symm g
  have hx : (coverPointsEquiv A a).symm (g ≫ q.hom.hom) =
      x ≫ ((baseChange U.hom).map q).hom.hom := by
    apply (coverPointsEquiv A a).injective
    rw [MulEquiv.apply_symm_apply, coverPointsEquiv_comp]
    change g ≫ q.hom.hom = (coverPointsEquiv G a
      ((coverPointsEquiv G a).symm g)) ≫ q.hom.hom
    rw [MulEquiv.apply_symm_apply]
  have hs' := congrArg (fun f : (baseChange U.hom).obj G ⟶
      (baseChange U.hom).obj B => f.hom.hom) hs
  change ((baseChange U.hom).map q).hom.hom ≫ d.hom.hom.hom =
    e.hom.hom.hom ≫ ((baseChange U.hom).map p).hom.hom at hs'
  change coverPointsEquiv B a
      ((coverPointsEquiv A a).symm (g ≫ q.hom.hom) ≫ d.hom.hom.hom) =
    coverPointsEquiv H a (x ≫ e.hom.hom.hom) ≫ p.hom.hom
  rw [hx, Category.assoc, hs', ← Category.assoc, coverPointsEquiv_comp]

end General
end LocalGroupIso

namespace IsAdjointQuotient

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H A B : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} {p : H ⟶ B}
    (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)
    (e : LocalGroupIso G H (Over.mk (algebraBaseMap k K)))

/-- A local family over a field extension induces a natural local family
between supplied full-centre adjoint quotients. -/
def localIso : LocalGroupIso A B (Over.mk (algebraBaseMap k K)) :=
  LocalGroupIso.ofBaseChangeIso
    ((adjointQuotientBaseChangeStatement.isAdjointQuotient hq).mapIso
      (adjointQuotientBaseChangeStatement.isAdjointQuotient hp) e.toBaseChangeIso)

/-- The induced family commutes with the quotient maps on all relative tests. -/
theorem localIso_square {T : Over (Spec (CommRingCat.of k))}
    (a : T ⟶ Over.mk (algebraBaseMap k K)) (g : T ⟶ G.X) :
    (hq.localIso hp e).toFun a (g ≫ q.hom.hom) =
      e.toFun a g ≫ p.hom.hom := by
  have h := LocalGroupIso.ofBaseChangeIso_square q p e.toBaseChangeIso
    ((adjointQuotientBaseChangeStatement.isAdjointQuotient hq).mapIso
      (adjointQuotientBaseChangeStatement.isAdjointQuotient hp) e.toBaseChangeIso)
    ((adjointQuotientBaseChangeStatement.isAdjointQuotient hq).comp_mapIso_hom
      (adjointQuotientBaseChangeStatement.isAdjointQuotient hp) e.toBaseChangeIso) a g
  rw [LocalGroupIso.ofBaseChangeIso_toBaseChangeIso] at h
  exact h

/-- The original and induced local families intertwine the actual inner actions,
including acting points that only lift fpqc locally. -/
theorem localIso_innerAction {T : Over (Spec (CommRingCat.of k))}
    (a : T ⟶ Over.mk (algebraBaseMap k K)) (x : T ⟶ A.X) (g : T ⟶ G.X) :
    e.toFun a (hq.innerAction.act x g) =
      hp.innerAction.act ((hq.localIso hp e).toFun a x) (e.toFun a g) := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x
  intro V b h hb
  rw [← e.naturality, hq.innerAction.naturality, hp.innerAction.naturality,
    ← (hq.localIso hp e).naturality, ← e.naturality,
    hb, hq.innerAction_act_lift, hq.localIso_square hp e, hp.innerAction_act_lift]
  simp only [map_mul, map_inv]

end IsAdjointQuotient
end Langlands.GroupScheme
