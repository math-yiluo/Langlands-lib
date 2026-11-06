import Langlands.GroupScheme.LocalGroupIsoBaseChange
import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery

/-! # Actual base-change isomorphisms classify natural local group isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- Natural local isomorphisms agree if their values agree on every relative test. -/
@[ext] theorem ext_toFun {e f : LocalGroupIso G H U}
    (h : ∀ (T : Over S) (a : T ⟶ U) (g : T ⟶ G.X),
      e.toFun a g = f.toFun a g) : e = f := by
  have hv : @e.toFun = @f.toFun := by
    funext T a
    exact MulEquiv.ext (h T a)
  cases e
  cases f
  cases hv
  rfl

/-- Recovering an actual isomorphism and passing back to local values recovers the family. -/
@[simp] theorem ofBaseChangeIso_toBaseChangeIso (e : LocalGroupIso G H U) :
    ofBaseChangeIso e.toBaseChangeIso = e := by
  apply ext_toFun
  intro T a g
  let x := (coverPointsEquiv G a).symm g
  have h := e.toBaseChangeIso_hom_points (coverTest a) x
  have hn := e.naturality (coverTestIso a).inv
    (baseChangeTestPoint (coverTest a))
    (baseChangePointsEquiv U.hom G (coverTest a) x)
  have ha : (coverTestIso a).inv ≫ baseChangeTestPoint (coverTest a) = a := by
    apply Over.OverMorphism.ext
    change 𝟙 T.left ≫ a.left = a.left
    exact Category.id_comp _
  rw [ha] at hn
  have hx : (coverTestIso a).inv ≫
      baseChangePointsEquiv U.hom G (coverTest a) x = g := by
    change coverPointsEquiv G a ((coverPointsEquiv G a).symm g) = g
    exact (coverPointsEquiv G a).apply_symm_apply g
  rw [hx] at hn
  change coverPointsEquiv H a (x ≫ e.toBaseChangeIso.hom.hom.hom) = e.toFun a g
  change (coverTestIso a).inv ≫
    baseChangePointsEquiv U.hom H (coverTest a)
      (x ≫ e.toBaseChangeIso.hom.hom.hom) = _
  rw [h]
  exact hn.symm

/-- Passing an actual isomorphism to local values and recovering it preserves it. -/
@[simp] theorem toBaseChangeIso_ofBaseChangeIso
    (f : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H) :
    (ofBaseChangeIso f).toBaseChangeIso = f := by
  symm
  apply (ofBaseChangeIso f).toBaseChangeIso_unique
  intro T x
  apply Over.OverMorphism.ext
  rw [baseChangePointsEquiv_left, ofBaseChangeIso_toFun_left]
  have hx : ((coverPointsEquiv G (baseChangeTestPoint T)).symm
      (baseChangePointsEquiv U.hom G T x)).left = x.left := by
    apply pullback.hom_ext
    · have hp := congrArg (fun q => q.left)
        ((coverPointsEquiv G (baseChangeTestPoint T)).apply_symm_apply
          (baseChangePointsEquiv U.hom G T x))
      rw [coverPointsEquiv_left, baseChangePointsEquiv_left] at hp
      exact hp
    · exact (Over.w _).trans (Over.w x).symm
  change x.left ≫ f.hom.hom.hom.left ≫ pullback.fst H.X.hom U.hom = _
  rw [hx]

/-- The all-relative-test interface is equivalent to an actual isomorphism over the cover. -/
def baseChangeIsoEquiv :
    ((baseChange U.hom).obj G ≅ (baseChange U.hom).obj H) ≃ LocalGroupIso G H U where
  toFun := ofBaseChangeIso
  invFun := toBaseChangeIso
  left_inv := toBaseChangeIso_ofBaseChangeIso
  right_inv := ofBaseChangeIso_toBaseChangeIso

end Langlands.GroupScheme.LocalGroupIso
