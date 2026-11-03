import Langlands.GroupScheme.AutomorphicAction.BaseChangeCompatibility
import Langlands.GroupScheme.Lie.BaseChange
import Langlands.GroupScheme.Lie.ActionDeterminant
import Langlands.GroupScheme.Rational.CharacterBaseChange

/-! # Actual differentials and determinant characters under base change -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    {H U : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "H_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) H
local notation "U_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) U

namespace AutomorphicAction

variable (a : AutomorphicAction H U)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- The actual affine pullback comparison intertwines the pulled-back action. -/
theorem affineBaseChangeEquiv_act
    (h : Lie.AffinePoints H_K A) (x : Lie.AffinePoints U_K A) :
    Lie.affineBaseChangeEquiv k K U A ((a.baseChange b).act h x) =
      a.act (Lie.affineBaseChangeEquiv k K H A h)
        (Lie.affineBaseChangeEquiv k K U A x) := by
  change (Lie.affineBaseTestIso k K A).inv ≫
      baseChangePointsEquiv b U _ ((a.baseChange b).act h x) =
    a.act ((Lie.affineBaseTestIso k K A).inv ≫ baseChangePointsEquiv b H _ h)
      ((Lie.affineBaseTestIso k K A).inv ≫ baseChangePointsEquiv b U _ x)
  rw [baseChangePointsEquiv_act, a.naturality]

/-- Constant acting points and the actual dual-number kernel agree under pullback. -/
theorem kernelBaseChangeEquiv_action
    (h : Lie.AffinePoints H_K A) (x : lieKernel U_K A) :
    Lie.kernelBaseChangeEquiv k K U A ((a.baseChange b).kernelAction h x) =
      a.kernelAction (Lie.affineBaseChangeEquiv k K H A h)
        (Lie.kernelBaseChangeEquiv k K U A x) := by
  apply Subtype.ext
  change Lie.affineBaseChangeEquiv k K U (DualNumber A)
      ((a.baseChange b).act (Lie.constant H_K h) x.val) =
    a.act (Lie.constant H (Lie.affineBaseChangeEquiv k K H A h))
      (Lie.affineBaseChangeEquiv k K U (DualNumber A) x.val)
  rw [affineBaseChangeEquiv_act, Lie.affineBaseChangeEquiv_constant]

variable [IsAffineHom U.X.hom]

local instance instActionBaseChangeAffineTarget : IsAffineHom (U_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd U.X.hom b)
  infer_instance

/-- The published linear comparison intertwines the actual action differentials. -/
theorem differential_baseChange
    (h : Lie.AffinePoints H_K A) (x : Additive (lieKernel U_K A)) :
    Lie.kernelBaseChangeLinearEquiv k K U A ((a.baseChange b).differential h x) =
      a.differential (Lie.affineBaseChangeEquiv k K H A h)
        (Lie.kernelBaseChangeLinearEquiv k K U A x) :=
  congrArg Additive.ofMul (a.kernelBaseChangeEquiv_action k K h x.toMul)

/-- Scheme base change preserves the determinant of the actual differential. -/
theorem differential_det_baseChange (h : Lie.AffinePoints H_K A) :
    LinearEquiv.det ((a.baseChange b).differential h) =
      LinearEquiv.det (a.differential (Lie.affineBaseChangeEquiv k K H A h)) := by
  let e := Lie.kernelBaseChangeLinearEquiv k K U A
  have he : e.symm.trans (((a.baseChange b).differential h).trans e) =
      a.differential (Lie.affineBaseChangeEquiv k K H A h) := by
    apply LinearEquiv.ext
    intro x
    change e ((a.baseChange b).differential h (e.symm x)) = _
    rw [differential_baseChange, LinearEquiv.apply_symm_apply]
  rw [← he]
  exact (LinearEquiv.det_conj ((a.baseChange b).differential h) e).symm

end AutomorphicAction

namespace rationalCharacters

variable (χ : rationalCharacters H)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- The pulled-back character has the original value under the affine comparison. -/
theorem characterEval_baseChange_affine (h : Lie.AffinePoints H_K A) :
    characterEval (baseChange b χ)
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) h =
      characterEval χ ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
        (Lie.affineBaseChangeEquiv k K H A h) := by
  rw [characterEval_baseChange]
  change _ = characterEval χ _
    ((Lie.affineBaseTestIso k K A).inv ≫ baseChangePointsEquiv b H _ h)
  rw [characterEval_naturality]
  change _ = Units.map
    (𝟙 _ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A)).appTop.hom.toMonoidHom _
  simp

end rationalCharacters

section FiniteBaseChange

variable [IsAffineHom U.X.hom]

local instance instLieActionBaseChangeAffineTarget : IsAffineHom (U_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd U.X.hom b)
  infer_instance

/-- Natural finite coordinates on the actual Lie kernels pull back with the same rank. -/
def Lie.FiniteCoordinates.baseChange {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    Lie.FiniteCoordinates U_K d where
  equiv A := by
    letI : Algebra k A := Algebra.compHom A (algebraMap k K)
    letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
    exact (Lie.kernelBaseChangeLinearEquiv k K U A).trans
      (c.equiv (CommAlgCat.of k A))
  naturality {A B} f x := by
    let : Algebra k A := Algebra.compHom A (algebraMap k K)
    let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra k B := Algebra.compHom B (algebraMap k K)
    let : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
    change c.equiv (CommAlgCat.of k B)
      (Lie.kernelBaseChangeLinearEquiv k K U B (lieKernelMapLinear U_K f.hom x)) = _
    rw [Lie.kernelBaseChangeLinearEquiv_naturality]
    exact c.naturality (CommAlgCat.ofHom (f.hom.restrictScalars k)) _

namespace AutomorphicAction

variable (a : AutomorphicAction H U) [IsAffine H.X.left]

local instance instActionBaseChangeAffineSource : IsAffine (H_K).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback H.X.hom b)
  infer_instance

variable {d : ℕ} (c : Lie.FiniteCoordinates U d)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- On every affine test, pulling back the actual determinant character gives the
determinant character of the pulled-back action, for any choices of coordinates. -/
theorem determinantCharacter_baseChange_eval_affine {e : ℕ}
    (cK : Lie.FiniteCoordinates U_K e) (h : Lie.AffinePoints H_K A) :
    characterEval (rationalCharacters.baseChange b (a.determinantCharacter c))
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) h =
      characterEval ((a.baseChange b).determinantCharacter cK)
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A))) h := by
  rw [rationalCharacters.characterEval_baseChange_affine k K,
    a.determinantCharacter_eval_affine c,
    (a.baseChange b).determinantCharacter_eval_affine cK]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom
      (LinearEquiv.det (a.differential (Lie.affineBaseChangeEquiv k K H A h))) =
    Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom
      (LinearEquiv.det ((a.baseChange b).differential h))
  exact congrArg
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)
    (a.differential_det_baseChange k K h).symm

/-- Actual rational determinant characters commute with scheme base change.
The equality is independent of the two finite-coordinate choices and their ranks. -/
theorem determinantCharacter_baseChange {e : ℕ} (cK : Lie.FiniteCoordinates U_K e) :
    rationalCharacters.baseChange b (a.determinantCharacter c) =
      (a.baseChange b).determinantCharacter cK := by
  apply rationalCharacters.ext_characterEval
  intro V x
  obtain ⟨⟨B⟩, ⟨i⟩⟩ :=
    (essImage_algSpec (G := (H_K).X)).mpr inferInstance
  let : Algebra k B := Algebra.compHom B (algebraMap k K)
  let : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  have hx : x = (x ≫ i.inv) ≫ i.hom := by simp
  rw [hx, characterEval_naturality, characterEval_naturality,
    determinantCharacter_baseChange_eval_affine k K a c cK i.hom]

end AutomorphicAction
end FiniteBaseChange

end Langlands.GroupScheme
