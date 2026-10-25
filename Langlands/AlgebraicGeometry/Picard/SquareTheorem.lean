import Langlands.AlgebraicGeometry.Picard.ShearClassification

/-! # The theorem of the square for Picard-zero families -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (classification : PicardZeroLineBundleClassificationStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (globalFunctions : Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions.{u})
variable {S : Scheme.{u}} (B : AbelianScheme S)

include classification stability globalFunctions in
/-- The theorem of the square: the pullback of a Picard-zero family along
`(t, b, b') ↦ (t, b * b')` is the tensor product of its pullbacks along
`(t, b, b') ↦ (t, b')` and `(t, b, b') ↦ (t, b)`. -/
theorem nonempty_shearBundle_iso (hB : HasDualScheme B) {T : Over S}
    (L : RigidifiedFamily B T) (hL : IsPicardZeroFamily B L) :
    Nonempty (shearBundle B L ≅ LineBundle.tensor preservation
      ((LineBundle.pullback ((relativeSpace B.X.hom).map (relativeFst B T))).obj
        ((RigidifiedLineBundle.forget _).obj L))
      ((LineBundle.pullback ((relativeProjection B.X.hom).app (relativeOver B T))).obj
        ((RigidifiedLineBundle.forget _).obj L))) := by
  obtain ⟨φ, ⟨e⟩⟩ := exists_shearBundle_iso preservation B hB classification stability L hL
  have hφ := eq_relativeFst_unitPoint_comp preservation stability globalFunctions hL e
  exact ⟨e ≪≫ LineBundle.tensorIso preservation
    (eqToIso (congrArg (poincarePullback B hB) hφ) ≪≫
      (poincarePullbackComp B hB (relativeFst B T) (unitPoint B T ≫ φ)).symm ≪≫
      (LineBundle.pullback _).mapIso (unitPointIso preservation e).symm) (Iso.refl _)⟩

/-- The point `(z, x)` of `T ×_S B` determined by `z : Z ⟶ T` and `x : Z ⟶ B`. -/
def pairOver {Z T : Over S} (z : Z ⟶ T) (x : Z ⟶ B.X) : Z ⟶ relativeOver B T :=
  Over.homMk (pullback.lift z.left x.left (by rw [Over.w z, Over.w x])) (by
    simp only [Over.mk_hom]
    rw [pullback.lift_fst_assoc, Over.w z])

@[simp] lemma pairOver_left {Z T : Over S} (z : Z ⟶ T) (x : Z ⟶ B.X) :
    (pairOver B z x).left = pullback.lift z.left x.left (by rw [Over.w z, Over.w x]) :=
  rfl

@[reassoc (attr := simp)]
lemma pairOver_fst {Z T : Over S} (z : Z ⟶ T) (x : Z ⟶ B.X) :
    pairOver B z x ≫ relativeFst B T = z := by
  ext
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairOver_snd {Z T : Over S} (z : Z ⟶ T) (x : Z ⟶ B.X) :
    pairOver B z x ≫ relativeSnd B T = x := by
  ext
  exact pullback.lift_snd _ _ _

lemma pairOver_shear {Z T : Over S} (z : Z ⟶ T) (x y : Z ⟶ B.X) :
    (pairOver B (pairOver B z x) y).left ≫ shear B (relativeFst B T) (relativeSnd B T) =
      (pairOver B z (x * y)).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, shear_fst, ← Category.assoc, pairOver_left, pullback.lift_fst,
      pairOver_left, pairOver_left, pullback.lift_fst, relativeFst_left, pullback.lift_fst]
  · rw [Category.assoc, shear_snd, ← Over.comp_left, MonObj.comp_mul, pairOver_fst_assoc,
      pairOver_snd, pairOver_snd, pairOver_left, pullback.lift_snd]

lemma pairOver_relativeFst {Z T : Over S} (z : Z ⟶ T) (x y : Z ⟶ B.X) :
    (pairOver B (pairOver B z x) y).left ≫ (relativeSpace B.X.hom).map (relativeFst B T) =
      (pairOver B z y).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeSpace_map_fst]
    change ((pairOver B (pairOver B z x) y ≫ relativeFst B _) ≫ relativeFst B T).left =
      (pairOver B z y ≫ relativeFst B T).left
    simp only [pairOver_fst]
  · rw [Category.assoc, relativeSpace_map_snd, ← relativeSnd_left, ← Over.comp_left,
      ← relativeSnd_left, ← Over.comp_left, pairOver_snd, pairOver_snd]

lemma pairOver_relativeProjection {Z T : Over S} (z : Z ⟶ T) (x y : Z ⟶ B.X) :
    (pairOver B (pairOver B z x) y).left ≫
        (relativeProjection B.X.hom).app (relativeOver B T) =
      (pairOver B z x).left := by
  change _ ≫ (relativeFst B (relativeOver B T)).left = _
  rw [← Over.comp_left, pairOver_fst]

include classification stability globalFunctions in
/-- The theorem of the square on points: for a Picard-zero family `L` on `T ×_S B`
and points `z`, `x`, `y`, the pullback of `L` along `(z, x * y)` is the tensor
product of its pullbacks along `(z, x)` and `(z, y)`. -/
theorem nonempty_pullback_pairOver_mul_iso (hB : HasDualScheme B) {Z T : Over S}
    (L : RigidifiedFamily B T) (hL : IsPicardZeroFamily B L) (z : Z ⟶ T) (x y : Z ⟶ B.X) :
    Nonempty ((LineBundle.pullback (pairOver B z (x * y)).left).obj
        ((RigidifiedLineBundle.forget _).obj L) ≅
      LineBundle.tensor preservation
        ((LineBundle.pullback (pairOver B z x).left).obj ((RigidifiedLineBundle.forget _).obj L))
        ((LineBundle.pullback (pairOver B z y).left).obj
          ((RigidifiedLineBundle.forget _).obj L))) := by
  obtain ⟨e⟩ := nonempty_shearBundle_iso preservation classification stability globalFunctions
    B hB L hL
  let χ := (pairOver B (pairOver B z x) y).left
  exact ⟨(LineBundle.pullbackCompEqIso χ _ (pairOver_shear B z x y) _).symm ≪≫
    (LineBundle.pullback χ).mapIso e ≪≫ LineBundle.pullbackTensorObjIso preservation χ _ _ ≪≫
    LineBundle.tensorIso preservation
      (LineBundle.pullbackCompEqIso χ _ (pairOver_relativeFst B z x y) _)
      (LineBundle.pullbackCompEqIso χ _ (pairOver_relativeProjection B z x y) _) ≪≫
    LineBundle.tensorCommIso preservation _ _⟩

end Langlands.AbelianScheme
