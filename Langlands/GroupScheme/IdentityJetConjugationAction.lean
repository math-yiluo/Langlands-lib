import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.IdentityJetSeparatedBaseChange
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws

/-! # The conjugation action on the actual identity neighborhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} (G : GroupScheme S) (n : ℕ)

/-- The closed inclusion of an identity neighborhood, as a morphism over the base. -/
def overInclusion : (schemeFunctor S n).obj G ⟶ G.X :=
  Over.homMk (inclusion G n)

instance : Mono (overInclusion G n) := by
  let : Mono (overInclusion G n).left := inferInstanceAs (Mono (inclusion G n))
  exact Over.mono_of_mono_left _

section

variable [IsSeparated G.X.hom] (U : Over S)

/-- Sections of the identity neighborhood of the pulled-back group are points
of the original identity neighborhood over the test scheme. -/
def baseChangedJetPoints :
    (Over.mk (𝟙 U.left) ⟶
      (schemeFunctor U.left n).obj ((GroupScheme.baseChange U.hom).obj G)) ≃
      (U ⟶ (schemeFunctor S n).obj G) := by
  let h := separatedBaseChange_isPullback G U.hom n
  refine
    { toFun := fun x => Over.homMk (x.left ≫ separatedBaseChangeMap G U.hom n) ?_
      invFun := fun x => Over.homMk
        (h.lift x.left (𝟙 _) (x.w.trans (Category.id_comp _).symm)) (h.lift_snd _ _ _)
      left_inv := ?_
      right_inv := ?_ }
  · change (x.left ≫ separatedBaseChangeMap G U.hom n) ≫ projection G n = U.hom
    have hx : x.left ≫ projection ((GroupScheme.baseChange U.hom).obj G) n = 𝟙 _ :=
      x.w
    rw [Category.assoc, h.w, ← Category.assoc, hx, Category.id_comp]
  · intro x
    apply Over.OverMorphism.ext
    apply h.hom_ext
    · exact h.lift_fst _ _ _
    · exact (h.lift_snd _ _ _).trans x.w.symm
  · intro x
    apply Over.OverMorphism.ext
    exact h.lift_fst _ _ _

private theorem baseChangedJetPoints_inclusion
    (x : Over.mk (𝟙 U.left) ⟶
      (schemeFunctor U.left n).obj ((GroupScheme.baseChange U.hom).obj G)) :
    baseChangedJetPoints G n U x ≫ overInclusion G n =
      baseChangeBasePointsEquiv U.hom G
        (x ≫ overInclusion ((GroupScheme.baseChange U.hom).obj G) n) := by
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, Over.comp_left, Over.comp_left]
  change (x.left ≫ separatedBaseChangeMap G U.hom n) ≫ inclusion G n =
    (x.left ≫ inclusion ((GroupScheme.baseChange U.hom).obj G) n) ≫
      pullback.fst G.X.hom U.hom
  simp only [Category.assoc, separatedBaseChangeMap_inclusion]

variable {U} in
/-- Conjugation by a test point on points of the same identity neighborhood. -/
def conjugatePoint (g : U ⟶ G.X) (x : U ⟶ (schemeFunctor S n).obj G) :
    U ⟶ (schemeFunctor S n).obj G :=
  baseChangedJetPoints G n U ((baseChangedJetPoints G n U).symm x ≫
    (conjugationAut ((GroupScheme.baseChange U.hom).obj G) n
      ((baseChangeBasePointsEquiv U.hom G).symm g)).asIso.hom)

variable {U} in
/-- The jet point obtained by conjugation has the prescribed image in the group. -/
@[reassoc]
theorem conjugatePoint_inclusion (g : U ⟶ G.X) (x : U ⟶ (schemeFunctor S n).obj G) :
    conjugatePoint G n g x ≫ overInclusion G n = g * (x ≫ overInclusion G n) * g⁻¹ := by
  let G' := (GroupScheme.baseChange U.hom).obj G
  let g' := (baseChangeBasePointsEquiv U.hom G).symm g
  have hc : (conjugationAut G' n g').asIso.hom ≫ overInclusion G' n =
      overInclusion G' n ≫ (G'.innerIso g').hom.hom.hom :=
    Over.OverMorphism.ext (conjugationAut_inclusion G' n g')
  rw [conjugatePoint, baseChangedJetPoints_inclusion, Category.assoc, hc, ← Category.assoc,
    comp_innerIso_hom, constantPoint_self, map_mul, map_mul, map_inv]
  change (baseChangeBasePointsEquiv U.hom G) g' *
      (baseChangeBasePointsEquiv U.hom G)
        ((baseChangedJetPoints G n U).symm x ≫ overInclusion G' n) *
      ((baseChangeBasePointsEquiv U.hom G) g')⁻¹ = _
  rw [← baseChangedJetPoints_inclusion, Equiv.apply_symm_apply]
  dsimp only [g']
  rw [MulEquiv.apply_symm_apply]

variable {U} in
/-- Conjugation on actual jet points commutes with restriction to every test scheme. -/
theorem conjugatePoint_naturality {V : Over S} (a : V ⟶ U)
    (g : U ⟶ G.X) (x : U ⟶ (schemeFunctor S n).obj G) :
    a ≫ conjugatePoint G n g x = conjugatePoint G n (a ≫ g) (a ≫ x) := by
  rw [← cancel_mono (overInclusion G n), Category.assoc, conjugatePoint_inclusion,
    conjugatePoint_inclusion, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

/-- The actual scheme action of the group on each of its identity neighborhoods. -/
@[instance_reducible]
def conjugationAction : SchemeAction G ((schemeFunctor S n).obj G) := by
  let J := (schemeFunctor S n).obj G
  let a : G.X ⊗ J ⟶ J := conjugatePoint G n (fst _ _) (snd _ _)
  have ha {U : Over S} (g : U ⟶ G.X) (x : U ⟶ J) :
      lift g x ≫ a = conjugatePoint G n g x := by
    change lift g x ≫ conjugatePoint G n (fst G.X J) (snd G.X J) = _
    dsimp only [J] at x ⊢
    simp only [conjugatePoint_naturality, lift_fst, lift_snd]
  refine schemeActionOfPointLaws a (fun x => ?_) (fun g h x => ?_)
  · rw [ha, ← cancel_mono (overInclusion G n), conjugatePoint_inclusion]
    simp
  · rw [ha, ha, ha, ← cancel_mono (overInclusion G n), conjugatePoint_inclusion,
      conjugatePoint_inclusion, conjugatePoint_inclusion]
    group

/-- The scheme action evaluates to conjugation on each test scheme. -/
theorem conjugationAction_act {U : Over S} (g : U ⟶ G.X)
    (x : U ⟶ (schemeFunctor S n).obj G) :
    (conjugationAction G n).act g x = conjugatePoint G n g x := by
  change lift g x ≫ conjugatePoint G n (fst _ _) (snd _ _) = _
  simp only [conjugatePoint_naturality, lift_fst, lift_snd]

end

end Langlands.GroupScheme.IdentityJet
