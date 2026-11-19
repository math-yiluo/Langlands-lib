import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.ComplexPermutationSwap
import Langlands.Representation.Archimedean.ComplexTransposeStandardDuality

/-! # The inverse-transpose dual of the complex local Whittaker model -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open Langlands.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

namespace ComplexLocalWhittakerDual

open ComplexReverseTwist
open Langlands.GeneralLinear

private theorem w0GL_eq_weylLong (n : ℕ) : w0GL n = weylLong n ℂ := by
  apply Units.ext
  ext i j
  rw [w0GL_val, w0Mat_apply, weylLong_entry]
  simp only [eq_comm]

private theorem conjAut_eq_inverseTranspose {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    conjAut g = inverseTranspose n ℂ g :=
  Units.ext rfl

private theorem dualFunction_eq_twistLin {n : ℕ} (W : Langlands.GeneralLinear n ℂ → ℂ) :
    ArchimedeanLocal.dualFunction n W = twistLin n W := by
  funext g
  rw [ArchimedeanLocal.dualFunction, twistLin_apply, ComplexReverseTwist.twist,
    w0GL_eq_weylLong, conjAut_eq_inverseTranspose]

private theorem twist_mul_upper {n : ℕ} (u : GeneralLinear.upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    ComplexReverseTwist.twist ((u : Langlands.GeneralLinear n ℂ) * g) =
      (w0GL n * conjAut (u : Langlands.GeneralLinear n ℂ) * w0GL n) *
        ComplexReverseTwist.twist g := by
  rw [twist_mul, ComplexReverseTwist.twist, ComplexReverseTwist.twist]
  simp only [mul_assoc]
  rw [← mul_assoc (w0GL n) (w0GL n), w0GL_mul_self, one_mul]

private theorem character_twist {r : ℕ} (a : ℂˣ)
    (u : GeneralLinear.upperUnipotent (r + 1) ℂ) :
    complexWhittakerCharacter a
      (w0GL (r + 1) * conjAut (u : Langlands.GeneralLinear (r + 1) ℂ) * w0GL (r + 1)) =
      complexWhittakerCharacter (-a) u.val := by
  have hentry (i : Fin r) :
      (w0GL (r + 1) * conjAut (u : Langlands.GeneralLinear (r + 1) ℂ) * w0GL (r + 1))
        i.castSucc i.succ = -u.val i.rev.castSucc i.rev.succ := by
    rw [w0GL_eq_weylLong, weylLong_conjugate_entry, conjAut_eq_inverseTranspose,
      inverseTranspose_entry, Fin.rev_castSucc, Fin.rev_succ]
    exact UpperUnipotent.inv_adjacent_entry u i.rev
  have hsum :
      (∑ i : Fin r,
        (w0GL (r + 1) * conjAut (u : Langlands.GeneralLinear (r + 1) ℂ) * w0GL (r + 1))
          i.castSucc i.succ) = -∑ i : Fin r, u.val i.castSucc i.succ := by
    simp only [hentry, Finset.sum_neg_distrib]
    congr 1
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  simp only [complexWhittakerCharacter, hsum,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply,
    Units.val_neg, mul_neg, neg_mul]

private theorem sum_sq_transpose_rev {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, ‖M j i.rev‖ ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl

private theorem sum_sq_rev_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, ‖M j.rev i‖ ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2 := by
  rw [Finset.sum_comm]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun j => rfl

private theorem height_twist {r : ℕ} (g : Langlands.GeneralLinear (r + 1) ℂ) :
    complexMatrixHeight (ComplexReverseTwist.twist g) = complexMatrixHeight g := by
  have hv (i j : Fin (r + 1)) : (ComplexReverseTwist.twist g) i j = g⁻¹ j i.rev := by
    rw [ComplexReverseTwist.twist, w0GL_eq_weylLong, weylLong_mul_entry,
      conjAut_eq_inverseTranspose, inverseTranspose_entry]
  have hi (i j : Fin (r + 1)) : (ComplexReverseTwist.twist g)⁻¹ i j = g j.rev i := by
    rw [ComplexReverseTwist.twist, w0GL_eq_weylLong, mul_inv_rev, weylLong_inv, mul_weylLong_entry,
      conjAut_apply, inv_inv]
    rfl
  simp only [complexMatrixHeight, Finset.sum_add_distrib, hv, hi,
    sum_sq_transpose_rev, sum_sq_rev_transpose]
  exact add_comm _ _

private theorem rightDerivative_twistLin {n : ℕ} {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X (twistLin n f) =
      twistLin n (rightDerivative (matrixModel ℂ n) (-X.transpose) f) :=
  funext (ComplexReverseIntertwinerTied.rightDerivative_twistLin hf X)

/-- The inverse characters in reversed order in the upper-Borel induced model. -/
def dualData (ds : List ComplexCharacterData) : List ComplexCharacterData :=
  ds.reverse.map ComplexCharacterData.inv

@[simp]
theorem length_dualData (ds : List ComplexCharacterData) : (dualData ds).length = ds.length := by
  simp [dualData]

private theorem position_dualData {n : ℕ} {ds : List ComplexCharacterData} (hd : ds.length = n)
    (j : Fin n) (z : ℂˣ) :
    complexPositionCharacter (dualData ds) j z = complexPositionCharacter ds j.rev z⁻¹ := by
  have hj : (j : ℕ) < (dualData ds).length := by simp [hd]
  have hir : (j.rev : ℕ) < ds.length := by simpa [hd] using j.rev.isLt
  rw [ComplexPermutation.complexPositionCharacter_eq_get _ _ hj,
    ComplexPermutation.complexPositionCharacter_eq_get _ _ hir]
  simp only [dualData, List.get_eq_getElem, List.getElem_map, List.getElem_reverse,
    ComplexCharacterData.inv_character_apply, map_inv, Units.val_inv_eq_inv_val]
  congr 3
  simp [hd, Fin.val_rev, Nat.sub_sub, Nat.add_comm]

private def standardTwist {n : ℕ} {ds : List ComplexCharacterData} (hd : ds.length = n) :
    Automorphic.complexStandardKFinite n ds ≃ₗ[ℂ]
      Automorphic.complexStandardKFinite n (dualData ds) :=
  ComplexTransposeStandardDuality.twistEquiv (position_dualData hd)

private def dualIntertwiner {r : ℕ} {ds : List ComplexCharacterData} (hd : ds.length = r + 1)
    (B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)) :
    Automorphic.complexStandardKFinite (r + 1) (dualData ds) →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
  (twistLin (r + 1)).comp (B.comp (standardTwist hd).symm.toLinearMap)

private theorem isComplexWhittakerIntertwiner_dual {r : ℕ} {ds : List ComplexCharacterData}
    (hd : ds.length = r + 1) {a : ℂˣ}
    {B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)} (hB : IsComplexWhittakerIntertwiner r ds a B) :
    IsComplexWhittakerIntertwiner r (dualData ds) (-a) (dualIntertwiner hd B) := by
  obtain ⟨hN, hSmooth, hGrowth, hK, hLie⟩ := hB
  let T := (standardTwist hd).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f u hu g
    change B (T f) (ComplexReverseTwist.twist (u * g)) =
      complexWhittakerCharacter (-a) u * B (T f) (ComplexReverseTwist.twist g)
    rw [twist_mul_upper ⟨u, hu⟩, hN (T f) _ (w0_conj_upperUnipotent ⟨u, hu⟩),
      character_twist a ⟨u, hu⟩]
  · intro f
    exact contMDiff_twistLin (hSmooth (T f))
  · intro f
    obtain ⟨C, N, h⟩ := hGrowth (T f)
    refine ⟨C, N, fun g => ?_⟩
    change ‖B (T f) (ComplexReverseTwist.twist g)‖ ≤ C * complexMatrixHeight g ^ N
    rw [← height_twist g]
    exact h (ComplexReverseTwist.twist g)
  · intro k f f' hf'
    change twistLin _ (B (T f')) =
      Whittaker.rightTranslation ℂ _ (k : Langlands.GeneralLinear (r + 1) ℂ)
        (twistLin _ (B (T f)))
    rw [rightTranslation_twistLin]
    congr 1
    apply hK (conjK _ k)
    change twistLin _ (f' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) =
      Whittaker.rightTranslation ℂ _ (conjAut (k : Langlands.GeneralLinear (r + 1) ℂ))
        (twistLin _ (f : Langlands.GeneralLinear (r + 1) ℂ → ℂ))
    rw [hf', rightTranslation_twistLin, conjAut_conjAut]
  · intro X f f' hf'
    change twistLin _ (B (T f')) =
      rightDerivative (matrixModel ℂ (r + 1)) X (twistLin _ (B (T f)))
    rw [rightDerivative_twistLin (hSmooth (T f))]
    congr 1
    apply hLie (-X.transpose)
    change twistLin _ (f' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) =
      rightDerivative (matrixModel ℂ (r + 1)) (-X.transpose)
        (twistLin _ (f : Langlands.GeneralLinear (r + 1) ℂ → ℂ))
    rw [hf', rightDerivative_twistLin f.2.1.1]
    simp only [Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]

/-- The exact dual in the local integrals is a Whittaker function for the reversed inverse
characters and the opposite additive character. -/
abbrev ComplexLocalWhittakerDualStatement : Prop :=
  ∀ {r : ℕ} {ds : List ComplexCharacterData}, ds.length = r + 1 →
    ∀ {a : ℂˣ} {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ},
      W ∈ complexWhittakerModel r ds a →
        ArchimedeanLocal.dualFunction (r + 1) W ∈ complexWhittakerModel r (dualData ds) (-a)

theorem dualFunction_mem : ComplexLocalWhittakerDualStatement := by
  intro r ds hd a W hW
  rw [dualFunction_eq_twistLin]
  have hle : complexWhittakerModel r ds a ≤
      (complexWhittakerModel r (dualData ds) (-a)).comap (twistLin (r + 1)) := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    change twistLin _ (B f) ∈ complexWhittakerModel r (dualData ds) (-a)
    have hdB := isComplexWhittakerIntertwiner_dual hd hB
    have hrange : LinearMap.range (dualIntertwiner hd B) ≤
        complexWhittakerModel r (dualData ds) (-a) :=
      le_iSup_of_le (dualIntertwiner hd B) (le_iSup_of_le hdB le_rfl)
    apply hrange
    refine ⟨standardTwist hd f, ?_⟩
    simp [dualIntertwiner]
  exact hle hW

end ComplexLocalWhittakerDual

end Langlands.Global.RankinSelbergGlobal
