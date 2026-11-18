import Langlands.GroupScheme.Cartier.RelativeHomFunctoriality
import Langlands.GroupScheme.Cartier.Characters
import Langlands.GroupScheme.IsomorphismSheaf
import Langlands.AlgebraicGeometry.EtaleLocalSystem
import Mathlib.CategoryTheory.Sites.SheafHom

/-! # Sheafness of actual relative homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier

open LocalGroupIso

variable {S : Scheme.{u}} (G H : CommGroupScheme S)

/-- A relative homomorphism acts on original points at any point of the test scheme. -/
def relativeHomLocalPoints {T V : Over S} (χ : RelativeHom G H T) (a : V ⟶ T) :
    (V ⟶ G.X) →* (V ⟶ H.X) :=
  (coverPointsEquiv H.toGrp a).toMonoidHom.comp
    ((((yonedaGrp.map χ.toMul).app (op (coverTest a))).hom).comp
      (coverPointsEquiv G.toGrp a).symm.toMonoidHom)

theorem relativeHomLocalPoints_naturality {T V W : Over S}
    (χ : RelativeHom G H T) (t : W ⟶ V) (a : V ⟶ T) (x : V ⟶ G.X) :
    relativeHomLocalPoints G H χ (t ≫ a) (t ≫ x) =
      t ≫ relativeHomLocalPoints G H χ a x := by
  change coverPointsEquiv H.toGrp (t ≫ a)
      ((coverPointsEquiv G.toGrp (t ≫ a)).symm (t ≫ x) ≫ χ.toMul.hom.hom) =
    t ≫ coverPointsEquiv H.toGrp a
      ((coverPointsEquiv G.toGrp a).symm x ≫ χ.toMul.hom.hom)
  rw [coverPointsEquiv_symm_naturality, Category.assoc, coverPointsEquiv_naturality]

/-- Actual relative homomorphisms give natural transformations of restricted point functors. -/
def relativeHomToLocalNatTrans (T : Over S) (χ : RelativeHom G H T) :
    (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T) where
  app V := GrpCat.ofHom (relativeHomLocalPoints G H χ V.unop.hom)
  naturality V W t := by
    ext x
    change relativeHomLocalPoints G H χ W.unop.hom (t.unop.left ≫ x) =
      t.unop.left ≫ relativeHomLocalPoints G H χ V.unop.hom x
    rw [← Over.w t.unop]
    exact relativeHomLocalPoints_naturality G H χ t.unop.left V.unop.hom x

/-- A local natural transformation acts on pullback points over the test scheme. -/
def localNatTransPoints {T : Over S}
    (α : (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T))
    (V : Over T.left) :
    (V ⟶ (testBaseChange T G).X) →* (V ⟶ (testBaseChange T H).X) :=
  (baseChangePointsEquiv T.hom H.toGrp V).symm.toMonoidHom.comp
    ((α.app (op (Over.mk (baseChangeTestPoint V)))).hom.comp
      (baseChangePointsEquiv T.hom G.toGrp V).toMonoidHom)

theorem localNatTransPoints_naturality {T : Over S}
    (α : (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T))
    {V W : Over T.left} (t : W ⟶ V) (x : V ⟶ (testBaseChange T G).X) :
    localNatTransPoints G H α W (t ≫ x) = t ≫ localNatTransPoints G H α V x := by
  apply (baseChangePointsEquiv T.hom H.toGrp W).injective
  change baseChangePointsEquiv T.hom H.toGrp W
      ((baseChangePointsEquiv T.hom H.toGrp W).symm
        ((α.app (op (Over.mk (baseChangeTestPoint W))))
          (baseChangePointsEquiv T.hom G.toGrp W (t ≫ x)))) =
    baseChangePointsEquiv T.hom H.toGrp W
      (t ≫ (baseChangePointsEquiv T.hom H.toGrp V).symm
        ((α.app (op (Over.mk (baseChangeTestPoint V))))
          (baseChangePointsEquiv T.hom G.toGrp V x)))
  rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
    baseChangePointsEquiv_naturality,
    MulEquiv.apply_symm_apply]
  let r : Over.mk (baseChangeTestPoint W) ⟶ Over.mk (baseChangeTestPoint V) :=
    Over.homMk ((Over.map T.hom).map t) (map_comp_baseChangeTestPoint t)
  exact ConcreteCategory.congr_hom (α.naturality r.op)
    (baseChangePointsEquiv T.hom G.toGrp V x)

/-- Yoneda recovers an actual relative homomorphism from a local natural transformation. -/
def localNatTransToRelativeHom {T : Over S}
    (α : (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T)) : RelativeHom G H T :=
  Additive.ofMul (homOfPoints (localNatTransPoints G H α)
    (localNatTransPoints_naturality G H α))

theorem localNatTransToRelativeHom_points {T : Over S}
    (α : (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T))
    (V : Over T.left) (x : V ⟶ (testBaseChange T G).X) :
    baseChangePointsEquiv T.hom H.toGrp V
      (x ≫ (localNatTransToRelativeHom G H α).toMul.hom.hom) =
        (α.app (op (Over.mk (baseChangeTestPoint V))))
          (baseChangePointsEquiv T.hom G.toGrp V x) := by
  change baseChangePointsEquiv T.hom H.toGrp V
    (x ≫ (homOfPoints (localNatTransPoints G H α)
      (localNatTransPoints_naturality G H α)).hom.hom) = _
  erw [comp_homOfPoints]
  exact (baseChangePointsEquiv T.hom H.toGrp V).apply_symm_apply _

theorem coverPointsEquiv_symm_left {T V : Over S} (a : V ⟶ T) (x : V ⟶ G.X) :
    ((coverPointsEquiv G.toGrp a).symm x).left =
      pullback.lift x.left a.left (by rw [Over.w x, Over.w a]) := by
  apply pullback.hom_ext
  · have h := congrArg (fun z => z.left) ((coverPointsEquiv G.toGrp a).apply_symm_apply x)
    exact h.trans (pullback.lift_fst _ _ _).symm
  · exact (Over.w _).trans (pullback.lift_snd _ _ _).symm

theorem relativeHomLocalPoints_left {T V : Over S}
    (χ : RelativeHom G H T) (a : V ⟶ T) (x : V ⟶ G.X) :
    (relativeHomLocalPoints G H χ a x).left =
      pullback.lift x.left a.left (by rw [Over.w x, Over.w a]) ≫
        CommGroupScheme.hom χ ≫ pullback.fst H.X.hom T.hom := by
  change (coverPointsEquiv H.toGrp a
    ((coverPointsEquiv G.toGrp a).symm x ≫ χ.toMul.hom.hom)).left = _
  rw [coverPointsEquiv_left, Over.comp_left, coverPointsEquiv_symm_left]
  rfl

theorem localNatTransToRelativeHom_toLocalNatTrans (T : Over S) (χ : RelativeHom G H T) :
    localNatTransToRelativeHom G H (relativeHomToLocalNatTrans G H T χ) = χ := by
  change (localNatTransToRelativeHom G H
    (relativeHomToLocalNatTrans G H T χ)).toMul = χ.toMul
  apply hom_ext_points
  intro V x
  apply (baseChangePointsEquiv T.hom H.toGrp V).injective
  erw [localNatTransToRelativeHom_points]
  apply Over.OverMorphism.ext
  change (relativeHomLocalPoints G H χ (baseChangeTestPoint V)
    (baseChangePointsEquiv T.hom G.toGrp V x)).left = _
  rw [relativeHomLocalPoints_left]
  have hx : x.left ≫ pullback.snd G.X.hom T.hom = V.hom := Over.w x
  have hlift : pullback.lift
      (baseChangePointsEquiv T.hom G.toGrp V x).left
      (baseChangeTestPoint V).left
      (by rw [Over.w, Over.w]) = x.left := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, baseChangePointsEquiv_left]
    · exact (pullback.lift_snd _ _ _).trans hx.symm
  rw [hlift, baseChangePointsEquiv_left, Over.comp_left, Category.assoc]

theorem relativeHomToLocalNatTrans_toRelativeHom {T : Over S}
    (α : (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T)) :
    relativeHomToLocalNatTrans G H T (localNatTransToRelativeHom G H α) = α := by
  apply NatTrans.ext
  funext V
  ext x
  let a := V.unop.hom
  let y := (coverPointsEquiv G.toGrp a).symm x
  have ha : (coverTestIso a).inv ≫ baseChangeTestPoint (coverTest a) = a := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  let r : V.unop ⟶ Over.mk (baseChangeTestPoint (coverTest a)) :=
    Over.homMk (coverTestIso a).inv ha
  have hn := ConcreteCategory.congr_hom (α.naturality r.op)
    (baseChangePointsEquiv T.hom G.toGrp (coverTest a) y)
  have hx : (coverTestIso a).inv ≫
      baseChangePointsEquiv T.hom G.toGrp (coverTest a) y = x :=
    (coverPointsEquiv G.toGrp a).apply_symm_apply x
  change coverPointsEquiv H.toGrp a
    (y ≫ (localNatTransToRelativeHom G H α).toMul.hom.hom) = _
  change (coverTestIso a).inv ≫ baseChangePointsEquiv T.hom H.toGrp (coverTest a)
    (y ≫ (localNatTransToRelativeHom G H α).toMul.hom.hom) = _
  rw [localNatTransToRelativeHom_points]
  change (α.app V) ((coverTestIso a).inv ≫
    baseChangePointsEquiv T.hom G.toGrp (coverTest a) y) = _ at hn
  rw [hx] at hn
  exact hn.symm

/-- The actual relative Hom group is equivalent, on underlying types, to
the local natural transformations of the group-valued point functors. -/
def relativeHomLocalNatEquiv (T : Over S) :
    RelativeHom G H T ≃
      (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).obj (op T) where
  toFun := relativeHomToLocalNatTrans G H T
  invFun := localNatTransToRelativeHom G H
  left_inv := localNatTransToRelativeHom_toLocalNatTrans G H T
  right_inv := relativeHomToLocalNatTrans_toRelativeHom G H

theorem relativeHomToLocalNatTrans_restrict {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) :
    relativeHomToLocalNatTrans G H T' (restrict G H a χ) =
      (presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)).map a.op
        (relativeHomToLocalNatTrans G H T χ) := by
  apply NatTrans.ext
  funext V
  ext x
  apply Over.OverMorphism.ext
  change (relativeHomLocalPoints G H (restrict G H a χ) V.unop.hom x).left =
    (relativeHomLocalPoints G H χ (V.unop.hom ≫ a) x).left
  rw [relativeHomLocalPoints_left, relativeHomLocalPoints_left, restrict_fst]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [baseChangeProj, Category.assoc]

/-- Actual relative homomorphisms satisfy descent for every subcanonical
topology on schemes over the base. -/
theorem isSheaf_relativeHomFunctor (J : GrothendieckTopology (Over S)) [J.Subcanonical] :
    Presheaf.IsSheaf J (relativeHomFunctor G H) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J (relativeHomFunctor G H)
    (forget AddCommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Presieve.isSheaf_iff_of_nat_equiv
    (fun {T} => relativeHomLocalNatEquiv G H T)
    (fun _ _ a χ => relativeHomToLocalNatTrans_restrict G H a χ)).2
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    ((LocalGroupIso.points_isSheaf J H.toGrp).hom (GroupScheme.points G.toGrp))

/-- Actual Cartier characters satisfy descent for every subcanonical topology. -/
theorem isSheaf_characters (J : GrothendieckTopology (Over S)) [J.Subcanonical] :
    Presheaf.IsSheaf J (characters G) :=
  isSheaf_relativeHomFunctor G (Gm S) J

/-- Actual Cartier characters are sheaves for the big relative étale topology. -/
theorem isEtaleSheaf_characters :
    Langlands.AlgebraicGeometry.EtaleLocalSystem.IsEtaleSheaf (characters G) := by
  let : Scheme.etaleTopology.Subcanonical :=
    .of_le (le_trans Scheme.etaleTopology_le_proetaleTopology
      Scheme.proetaleTopology_le_fpqcTopology)
  exact isSheaf_characters G (Langlands.AlgebraicGeometry.EtaleLocalSystem.topology S)

end Langlands.GroupScheme.Cartier
