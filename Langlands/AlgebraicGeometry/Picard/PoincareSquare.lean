import Langlands.AlgebraicGeometry.Picard.TranslationBaseChange
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackStatement

/-! # Shear maps and the Poincaré square -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (B : AbelianScheme S)

/-- The product `Y ×_S B`, as a scheme over `S` through `Y`. -/
abbrev relativeOver (Y : Over S) : Over S :=
  Over.mk (pullback.fst Y.hom B.X.hom ≫ Y.hom)

/-- The first projection `Y ×_S B ⟶ Y` over `S`. -/
def relativeFst (Y : Over S) : relativeOver B Y ⟶ Y :=
  Over.homMk (pullback.fst Y.hom B.X.hom) rfl

/-- The second projection `Y ×_S B ⟶ B` over `S`. -/
def relativeSnd (Y : Over S) : relativeOver B Y ⟶ B.X :=
  Over.homMk (pullback.snd Y.hom B.X.hom) pullback.condition.symm

@[simp] lemma relativeFst_left (Y : Over S) :
    (relativeFst B Y).left = pullback.fst Y.hom B.X.hom := rfl

@[simp] lemma relativeSnd_left (Y : Over S) :
    (relativeSnd B Y).left = pullback.snd Y.hom B.X.hom := rfl

/-- The identity point of `B` on a test scheme is the unit section. -/
lemma one_left (Y : Over S) : (1 : Y ⟶ B.X).left = Y.hom ≫ unitSection B := by
  have h := congrArg (fun k : Y ⟶ B.X ↦ k.left)
    (MonObj.comp_one (M := B.X) (Over.mkIdTerminal.from Y))
  simp only [Over.comp_left, Over.mkIdTerminal_from_left] at h
  exact h.symm

@[reassoc (attr := simp)]
lemma relativeSpace_map_fst {Y T : Over S} (a : Y ⟶ T) :
    (relativeSpace B.X.hom).map a ≫ pullback.fst T.hom B.X.hom =
      pullback.fst Y.hom B.X.hom ≫ a.left :=
  (relativeProjection B.X.hom).naturality a

@[reassoc (attr := simp)]
lemma relativeSpace_map_snd {Y T : Over S} (a : Y ⟶ T) :
    (relativeSpace B.X.hom).map a ≫ pullback.snd T.hom B.X.hom =
      pullback.snd Y.hom B.X.hom :=
  pullback.lift_snd _ _ _

/-- The map `Y' ×_S B ⟶ Y ×_S B` over `S` induced by `h : Y' ⟶ Y`. -/
def relativeMap {Y' Y : Over S} (h : Y' ⟶ Y) : relativeOver B Y' ⟶ relativeOver B Y :=
  Over.homMk ((relativeSpace B.X.hom).map h) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, relativeSpace_map_fst, Category.assoc, Over.w])

@[simp] lemma relativeMap_left {Y' Y : Over S} (h : Y' ⟶ Y) :
    (relativeMap B h).left = (relativeSpace B.X.hom).map h := rfl

@[reassoc (attr := simp)]
lemma relativeMap_fst {Y' Y : Over S} (h : Y' ⟶ Y) :
    relativeMap B h ≫ relativeFst B Y = relativeFst B Y' ≫ h := by
  ext
  simp only [Over.comp_left, relativeMap_left, relativeFst_left, relativeSpace_map_fst]

@[reassoc (attr := simp)]
lemma relativeMap_snd {Y' Y : Over S} (h : Y' ⟶ Y) :
    relativeMap B h ≫ relativeSnd B Y = relativeSnd B Y' := by
  ext
  simp only [Over.comp_left, relativeMap_left, relativeSnd_left, relativeSpace_map_snd]

/-- The shear map `(y, b) ↦ (a y, c y * b)` from `Y ×_S B` to `T ×_S B`. -/
def shear {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X) :
    (relativeSpace B.X.hom).obj Y ⟶ (relativeSpace B.X.hom).obj T :=
  pullback.lift (pullback.fst Y.hom B.X.hom ≫ a.left)
    ((relativeFst B Y ≫ c) * relativeSnd B Y).left
    (by
      rw [Category.assoc, Over.w a]
      exact (Over.w ((relativeFst B Y ≫ c) * relativeSnd B Y)).symm)

@[reassoc (attr := simp)]
lemma shear_fst {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X) :
    shear B a c ≫ pullback.fst T.hom B.X.hom = pullback.fst Y.hom B.X.hom ≫ a.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma shear_snd {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X) :
    shear B a c ≫ pullback.snd T.hom B.X.hom =
      ((relativeFst B Y ≫ c) * relativeSnd B Y).left :=
  pullback.lift_snd _ _ _

/-- Shear maps are natural in the source. -/
lemma relativeSpace_map_shear {Y' Y T : Over S} (h : Y' ⟶ Y) (a : Y ⟶ T) (c : Y ⟶ B.X) :
    (relativeSpace B.X.hom).map h ≫ shear B a c = shear B (h ≫ a) (h ≫ c) := by
  apply pullback.hom_ext
  · rw [Category.assoc, shear_fst, shear_fst, ← Category.assoc, relativeSpace_map_fst,
      Category.assoc, Over.comp_left]
  · rw [Category.assoc, shear_snd, shear_snd, ← relativeMap_left, ← Over.comp_left,
      MonObj.comp_mul, relativeMap_fst_assoc, relativeMap_snd]

/-- Shearing by the identity point is the induced map of products. -/
lemma shear_one {Y T : Over S} (a : Y ⟶ T) :
    shear B a 1 = (relativeSpace B.X.hom).map a := by
  apply pullback.hom_ext
  · rw [shear_fst, relativeSpace_map_fst]
  · rw [shear_snd, MonObj.comp_one, one_mul, relativeSpace_map_snd, relativeSnd_left]

/-- Restricting a shear map along the unit section. -/
lemma relativeSection_shear {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X) :
    (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app Y ≫ shear B a c =
      pullback.lift a.left c.left (by rw [Over.w a, Over.w c]) := by
  let σ : Y ⟶ relativeOver B Y :=
    Over.homMk ((relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app Y)
      (by
        simp only [Over.mk_hom]
        rw [← Category.assoc]
        exact congrArg (· ≫ Y.hom)
          (relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) Y) |>.trans
            (Category.id_comp _))
  have h1 : σ ≫ relativeFst B Y = 𝟙 Y := by
    ext
    exact relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) Y
  have h2 : σ ≫ relativeSnd B Y = 1 := by
    ext
    rw [Over.comp_left, one_left]
    exact relativeSection_snd B.X.hom (unitSection B) (unitSection_comp B) Y
  apply pullback.hom_ext
  · rw [Category.assoc, shear_fst, ← Category.assoc, pullback.lift_fst]
    exact (congrArg (· ≫ a.left)
      (relativeSection_projection B.X.hom (unitSection B) (unitSection_comp B) Y)).trans
        (Category.id_comp _)
  · rw [Category.assoc, shear_snd, pullback.lift_snd]
    change (σ ≫ ((relativeFst B Y ≫ c) * relativeSnd B Y)).left = c.left
    rw [MonObj.comp_mul, ← Category.assoc, h1, h2, Category.id_comp, mul_one]

/-- The section of the base change `B_Y` determined by a point `c : Y ⟶ B`. -/
def pointSection {Y : Over S} (c : Y ⟶ B.X) :
    Over.mk (𝟙 Y.left) ⟶ ((Over.pullback Y.hom).mapGrp.obj B.toGrp).X :=
  (GroupScheme.baseChangePointsEquiv Y.hom B.toGrp (Over.mk (𝟙 Y.left))).symm
    (Over.homMk c.left (by simp))

/-- A shear map on the conventional total space `B ×_S Y`, recognized from the two
components of a self-map of `B ×_S Y`. -/
lemma shear_eq_of_comp {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X)
    (t : pullback B.X.hom Y.hom ⟶ pullback B.X.hom Y.hom)
    (h1 : t ≫ pullback.snd B.X.hom Y.hom = pullback.snd B.X.hom Y.hom)
    (h2 : t ≫ pullback.fst B.X.hom Y.hom =
      (relativeSpaceSymmetry B.X.hom Y).inv ≫ ((relativeFst B Y ≫ c) * relativeSnd B Y).left) :
    (relativeSpaceSymmetry B.X.hom Y).inv ≫ shear B a c =
      t ≫ (relativeSpaceSymmetry B.X.hom Y).inv ≫ (relativeSpace B.X.hom).map a := by
  have e1 : (relativeSpaceSymmetry B.X.hom Y).inv ≫ pullback.fst Y.hom B.X.hom =
      pullback.snd B.X.hom Y.hom :=
    pullbackSymmetry_inv_comp_fst _ _
  have e2 : (relativeSpaceSymmetry B.X.hom Y).inv ≫ pullback.snd Y.hom B.X.hom =
      pullback.fst B.X.hom Y.hom :=
    pullbackSymmetry_inv_comp_snd _ _
  apply pullback.hom_ext
  · rw [Category.assoc, shear_fst, reassoc_of% e1, Category.assoc, Category.assoc,
      relativeSpace_map_fst, reassoc_of% e1, reassoc_of% h1]
  · rw [Category.assoc, shear_snd, Category.assoc, Category.assoc, relativeSpace_map_snd, e2, h2]

/-- The total space of `B_Y`, viewed over `S`, as the product `Y ×_S B`. -/
def symmetryOver (Y : Over S) :
    (Over.map Y.hom).obj ((Over.pullback Y.hom).mapGrp.obj B.toGrp).X ⟶ relativeOver B Y :=
  Over.homMk (relativeSpaceSymmetry B.X.hom Y).inv (by
    change (pullbackSymmetry Y.hom B.X.hom).inv ≫ pullback.fst Y.hom B.X.hom ≫ Y.hom =
      pullback.snd B.X.hom Y.hom ≫ Y.hom
    rw [pullbackSymmetry_inv_comp_fst_assoc])

lemma symmetryOver_fst {Y : Over S} (c : Y ⟶ B.X) :
    symmetryOver B Y ≫ relativeFst B Y ≫ c =
      (Over.map Y.hom).map (Over.mkIdTerminal.from _) ≫
        (Over.homMk c.left (by simp) :
          (Over.map Y.hom).obj (Over.mk (𝟙 Y.left)) ⟶ B.X) := by
  ext
  rw [Over.comp_left, Over.comp_left, Over.comp_left, Over.map_map_left,
    Over.mkIdTerminal_from_left]
  have e1 : (symmetryOver B Y).left = (pullbackSymmetry Y.hom B.X.hom).inv := rfl
  have e2 : ((Over.pullback Y.hom).mapGrp.obj B.toGrp).X.hom = pullback.snd B.X.hom Y.hom := rfl
  rw [e1, e2, relativeFst_left]
  exact pullbackSymmetry_inv_comp_fst_assoc Y.hom B.X.hom c.left

lemma symmetryOver_snd (Y : Over S) :
    symmetryOver B Y ≫ relativeSnd B Y =
      GroupScheme.baseChangePointsEquiv Y.hom B.toGrp _ (𝟙 _) := by
  ext
  change (pullbackSymmetry Y.hom B.X.hom).inv ≫ pullback.snd Y.hom B.X.hom =
    𝟙 _ ≫ pullback.fst B.X.hom Y.hom
  rw [pullbackSymmetry_inv_comp_snd, Category.id_comp]

/-- On the conventional total space `B ×_S Y`, a shear map is a translation of
`B_Y` followed by the induced map of products. -/
lemma relativeSpaceSymmetry_inv_shear {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X) :
    (relativeSpaceSymmetry B.X.hom Y).inv ≫ shear B a c =
      (GroupScheme.translation ((Over.pullback Y.hom).mapGrp.obj B.toGrp)
          (pointSection B c)).left ≫
        (relativeSpaceSymmetry B.X.hom Y).inv ≫ (relativeSpace B.X.hom).map a := by
  have hp : GroupScheme.baseChangePointsEquiv Y.hom B.toGrp (Over.mk (𝟙 Y.left))
      (pointSection B c) = (Over.homMk c.left (by simp) :
        (Over.map Y.hom).obj (Over.mk (𝟙 Y.left)) ⟶ B.X) :=
    MulEquiv.apply_symm_apply _ _
  have h := GroupScheme.baseChangePointsEquiv_translation Y.hom B.toGrp (pointSection B c)
  rw [hp, ← symmetryOver_fst B c, ← symmetryOver_snd, ← MonObj.comp_mul] at h
  exact shear_eq_of_comp B a c _ (Over.w _) (congrArg (fun k ↦ k.left) h)

/-- The line-bundle form of `relativeSpaceSymmetry_inv_shear`. -/
def shearTranslationIso {Y T : Over S} (a : Y ⟶ T) (c : Y ⟶ B.X)
    (F : LineBundle ((relativeSpace B.X.hom).obj T)) :
    (LineBundle.pullback (relativeSpaceSymmetry B.X.hom Y).inv).obj
        ((LineBundle.pullback (shear B a c)).obj F) ≅
      (LineBundle.pullback (GroupScheme.translation ((Over.pullback Y.hom).mapGrp.obj B.toGrp)
          (pointSection B c)).left).obj
        ((LineBundle.pullback (relativeSpaceSymmetry B.X.hom Y).inv).obj
          ((LineBundle.pullback ((relativeSpace B.X.hom).map a)).obj F)) :=
  LineBundle.pullbackCompEqIso _ _ (relativeSpaceSymmetry_inv_shear B a c) F ≪≫
    (LineBundle.pullbackCompEqIso _ _ rfl F).symm ≪≫
    (LineBundle.pullback _).mapIso (LineBundle.pullbackCompEqIso _ _ rfl F).symm

/-- Pulling a Picard-zero family back along a shear map gives a bundle that is
Picard-zero on geometric fibres. -/
lemma isGeometricallyPicardZero_shear (stability : PicardZeroPullbackStatement.{u})
    {Y T : Over S} (L : RigidifiedFamily B T) (hL : IsPicardZeroFamily B L)
    (a : Y ⟶ T) (c : Y ⟶ B.X) :
    IsGeometricallyPicardZero ((baseChange Y.hom).obj B)
      ((LineBundle.pullback (relativeSpaceSymmetry B.X.hom Y).inv).obj
        ((LineBundle.pullback (shear B a c)).obj ((RigidifiedLineBundle.forget _).obj L))) := by
  have h := isGeometricallyPicardZero_pullback_translation ((baseChange Y.hom).obj B)
    (stability S B Y T a L hL) (pointSection B c)
  exact isGeometricallyPicardZero_of_iso _ (shearTranslationIso B a c _).symm h

end Langlands.AbelianScheme
