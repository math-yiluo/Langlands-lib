import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.Torsion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier

universe u
variable {S : Scheme.{u}}

/-- The identity section, regarded over the original base, is the original test scheme. -/
def sectionBaseIso (T : Over S) :
    (Over.map T.hom).obj (Over.mk (𝟙 T.left)) ≅ T :=
  Over.isoMk (Iso.refl _) (by simp)

/-- Sections of the actual pullback group scheme are the original test-scheme points. -/
def sectionPointsEquiv (G : CommGroupScheme S) (T : Over S) :
    (Over.mk (𝟙 T.left) ⟶ ((CommGroupScheme.baseChange T.hom).obj G).X) ≃*
      (T ⟶ G.X) :=
  (baseChangePointsEquiv T.hom G.toGrp (Over.mk (𝟙 T.left))).trans
    (((yonedaGrpObj G.X).mapIso (sectionBaseIso T).symm.op).groupIsoToMulEquiv)

@[simp] lemma sectionPointsEquiv_left (G : CommGroupScheme S) (T : Over S)
    (x : Over.mk (𝟙 T.left) ⟶ ((CommGroupScheme.baseChange T.hom).obj G).X) :
    (sectionPointsEquiv G T x).left = x.left ≫ pullback.fst G.X.hom T.hom := by
  change 𝟙 T.left ≫ (x.left ≫ pullback.fst G.X.hom T.hom) = _
  simp

/-- Relative homomorphisms are actual homomorphisms of the pullback group schemes. -/
abbrev RelativeHom (G H : CommGroupScheme S) (T : Over S) :=
  (CommGroupScheme.baseChange T.hom).obj G ⟶ (CommGroupScheme.baseChange T.hom).obj H

/-- Evaluate a relative homomorphism on the section corresponding to a point. -/
def evaluation {G H : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) : (T ⟶ G.X) →* (T ⟶ H.X) :=
  (sectionPointsEquiv H T).toMonoidHom.comp
    (((yonedaGrp.map χ.toMul).app (op (Over.mk (𝟙 T.left)))).hom.comp
      (sectionPointsEquiv G T).symm.toMonoidHom)

lemma evaluation_def {G H : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    evaluation χ x = sectionPointsEquiv H T
      ((sectionPointsEquiv G T).symm x ≫ χ.toMul.hom.hom) := rfl

@[simp] lemma evaluation_one {G H : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) : evaluation χ 1 = 1 := map_one _

@[simp] lemma evaluation_mul {G H : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) (x y : T ⟶ G.X) :
    evaluation χ (x * y) = evaluation χ x * evaluation χ y := map_mul _ _ _

@[simp] lemma evaluation_inv {G H : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    evaluation χ x⁻¹ = (evaluation χ x)⁻¹ := map_inv _ _

@[simp] lemma evaluation_zero {G H : CommGroupScheme S} {T : Over S}
    (x : T ⟶ G.X) : evaluation (0 : RelativeHom G H T) x = 1 := by
  simp [evaluation_def]

@[simp] lemma evaluation_add {G H : CommGroupScheme S} {T : Over S}
    (χ ψ : RelativeHom G H T) (x : T ⟶ G.X) :
    evaluation (χ + ψ) x = evaluation χ x * evaluation ψ x := by
  change sectionPointsEquiv H T
    ((sectionPointsEquiv G T).symm x ≫ (χ.toMul * ψ.toMul).hom.hom) = _
  simp [MonObj.comp_mul, evaluation_def]

@[simp] lemma evaluation_neg {G H : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    evaluation (-χ) x = (evaluation χ x)⁻¹ := by
  change sectionPointsEquiv H T
    ((sectionPointsEquiv G T).symm x ≫ χ.toMul⁻¹.hom.hom) = _
  simp [GrpObj.comp_inv, evaluation_def]

/-- Evaluation is additive in the relative homomorphism, with target in additive notation. -/
def evaluationAddHom (G H : CommGroupScheme S) (T : Over S) (x : T ⟶ G.X) :
    RelativeHom G H T →+ Additive (T ⟶ H.X) where
  toFun χ := Additive.ofMul (evaluation χ x)
  map_zero' := evaluation_zero x
  map_add' χ ψ := evaluation_add χ ψ x

@[simp] lemma evaluation_id (G : CommGroupScheme S) (T : Over S) (x : T ⟶ G.X) :
    evaluation (𝟙 ((CommGroupScheme.baseChange T.hom).obj G)) x = x := by
  change sectionPointsEquiv G T ((sectionPointsEquiv G T).symm x ≫ 𝟙 _) = x
  simp

@[simp] lemma evaluation_comp {G H K : CommGroupScheme S} {T : Over S}
    (χ : RelativeHom G H T) (ψ : RelativeHom H K T) (x : T ⟶ G.X) :
    evaluation (χ ≫ ψ) x = evaluation ψ (evaluation χ x) := by
  simp only [evaluation_def, MulEquiv.symm_apply_apply]
  change sectionPointsEquiv K T (_ ≫ (χ.toMul.hom.hom ≫ ψ.toMul.hom.hom)) =
    sectionPointsEquiv K T ((_ ≫ χ.toMul.hom.hom) ≫ ψ.toMul.hom.hom)
  rw [Category.assoc]

lemma sectionPointsEquiv_comp {G H : CommGroupScheme S} (f : G ⟶ H) (T : Over S)
    (x : Over.mk (𝟙 T.left) ⟶ ((CommGroupScheme.baseChange T.hom).obj G).X) :
    sectionPointsEquiv H T
      (x ≫ ((CommGroupScheme.baseChange T.hom).map f).toMul.hom.hom) =
      sectionPointsEquiv G T x ≫ f.toMul.hom.hom := by
  apply Over.OverMorphism.ext
  simp only [sectionPointsEquiv_left, Over.comp_left]
  change (x.left ≫ ((Over.pullback T.hom).map f.toMul.hom.hom).left) ≫ _ = _
  simp [Category.assoc]

/-- A global homomorphism evaluated after base change acts by ordinary postcomposition. -/
@[simp] lemma evaluation_baseChange {G H : CommGroupScheme S} (f : G ⟶ H)
    (T : Over S) (x : T ⟶ G.X) :
    evaluation ((CommGroupScheme.baseChange T.hom).map f) x = x ≫ f.toMul.hom.hom := by
  rw [evaluation_def, sectionPointsEquiv_comp, MulEquiv.apply_symm_apply]

/-- Precomposition in the source is compatible with evaluation. -/
lemma evaluation_precompose {G' G H : CommGroupScheme S} (f : G' ⟶ G)
    {T : Over S} (χ : RelativeHom G H T) (x : T ⟶ G'.X) :
    evaluation ((CommGroupScheme.baseChange T.hom).map f ≫ χ) x =
      evaluation χ (x ≫ f.toMul.hom.hom) := by simp

/-- Postcomposition in the target is compatible with evaluation. -/
lemma evaluation_postcompose {G H H' : CommGroupScheme S} (f : H ⟶ H')
    {T : Over S} (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    evaluation (χ ≫ (CommGroupScheme.baseChange T.hom).map f) x =
      evaluation χ x ≫ f.toMul.hom.hom := by simp

/-- An annihilated group scheme has annihilated points on every test scheme. -/
lemma points_zpow_eq_one (G : CommGroupScheme S) (n : ℤ)
    (h : multiplication G.toGrp n = 1) (T : Over S) (x : T ⟶ G.X) : x ^ n = 1 := by
  rw [← points_multiplication G.toGrp n T x, h]
  simp

/-- Evaluation is annihilated whenever its source group scheme is annihilated. -/
lemma evaluation_zpow_eq_one {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) : (evaluation χ x) ^ n = 1 := by
  rw [← map_zpow, points_zpow_eq_one G n h T x, map_one]

/-- Canonical evaluation into the actual torsion subgroup scheme of the target. -/
def torsionEvaluation {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) : T ⟶ (torsion H.toGrp n).X :=
  (torsionPointsEquiv H.toGrp n T).symm
    ⟨evaluation χ x, (mem_torsionPoints H.toGrp n T _).mpr
      (evaluation_zpow_eq_one n h χ x)⟩

/-- Inclusion of the torsion-valued evaluation recovers ordinary evaluation. -/
@[simp] lemma torsionEvaluation_ι {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    torsionEvaluation n h χ x ≫ (torsionι H.toGrp n).hom.hom = evaluation χ x :=
  congrArg Subtype.val ((torsionPointsEquiv H.toGrp n T).apply_symm_apply _)

/-- The torsion kernel universal property uniquely determines this lift. -/
lemma torsionEvaluation_unique {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) (y : T ⟶ (torsion H.toGrp n).X)
    (hy : y ≫ (torsionι H.toGrp n).hom.hom = evaluation χ x) :
    y = torsionEvaluation n h χ x := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  rw [hy, torsionEvaluation_ι]

@[simp] lemma torsionEvaluation_mul {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x y : T ⟶ G.X) :
    torsionEvaluation n h χ (x * y) =
      torsionEvaluation n h χ x * torsionEvaluation n h χ y := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  simp [MonObj.mul_comp]

@[simp] lemma torsionEvaluation_add {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ ψ : RelativeHom G H T) (x : T ⟶ G.X) :
    torsionEvaluation n h (χ + ψ) x =
      torsionEvaluation n h χ x * torsionEvaluation n h ψ x := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  simp [MonObj.mul_comp]

@[simp] lemma torsionEvaluation_one {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) : torsionEvaluation n h χ 1 = 1 := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  simp

@[simp] lemma torsionEvaluation_inv {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    torsionEvaluation n h χ x⁻¹ = (torsionEvaluation n h χ x)⁻¹ := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  simp [GrpObj.inv_comp]

@[simp] lemma torsionEvaluation_zero {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S} (x : T ⟶ G.X) :
    torsionEvaluation n h (0 : RelativeHom G H T) x = 1 := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  simp

@[simp] lemma torsionEvaluation_neg {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T : Over S}
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    torsionEvaluation n h (-χ) x = (torsionEvaluation n h χ x)⁻¹ := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  simp [GrpObj.inv_comp]

end Langlands.GroupScheme.Cartier
