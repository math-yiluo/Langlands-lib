import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.ComplexTransposeStandardDuality
import Langlands.Representation.Whittaker.DualTransform

/-! # Inverse-transpose transport of complex local Whittaker models -/

noncomputable section

open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.Automorphic Langlands.LocalFactor.Archimedean Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.GeneralLinear

private theorem twist_eq_weylInverseTranspose {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    ComplexReverseTwist.twist g = weylInverseTranspose n ℂ g := by
  have hw : w0GL n = weylLong n ℂ := by
    apply Units.ext
    ext i j
    simp only [w0GL_val, w0Mat_apply, weylLong_entry, eq_comm]
  rw [ComplexReverseTwist.twist, weylInverseTranspose_apply, hw]
  rfl

private theorem dualFunction_eq_twistLin {n : ℕ} (W : Langlands.GeneralLinear n ℂ → ℂ) :
    ArchimedeanLocal.dualFunction n W = twistLin n W := by
  funext g
  exact congrArg W (twist_eq_weylInverseTranspose g).symm

private theorem complexMatrixHeight_twist {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    complexMatrixHeight (ComplexReverseTwist.twist g) = complexMatrixHeight g := by
  have hInv (i j : Fin n) : ((weylInverseTranspose n ℂ g)⁻¹ : Langlands.GeneralLinear n ℂ) i j =
      g j.rev i := by
    rw [weylInverseTranspose_apply, _root_.mul_inv_rev, weylLong_inv, ← map_inv,
      mul_weylLong_entry, inverseTranspose_entry, inv_inv]
  have hRow (A : Matrix (Fin n) (Fin n) ℂ) :
      (∑ i : Fin n, ∑ j : Fin n, ‖A j i.rev‖ ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 :=
    (Equiv.sum_comp Fin.revPerm (fun i => ∑ j : Fin n, ‖A j i‖ ^ 2)).trans Finset.sum_comm
  have hCol (A : Matrix (Fin n) (Fin n) ℂ) :
      (∑ i : Fin n, ∑ j : Fin n, ‖A j.rev i‖ ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
    simp_rw [show ∀ i : Fin n, (∑ j : Fin n, ‖A j.rev i‖ ^ 2) = ∑ j : Fin n, ‖A j i‖ ^ 2
      from fun i => Equiv.sum_comp Fin.revPerm (fun j => ‖A j i‖ ^ 2)]
    exact Finset.sum_comm
  rw [twist_eq_weylInverseTranspose]
  simp only [complexMatrixHeight, Finset.sum_add_distrib, weylInverseTranspose_entry, hInv,
    hRow, hCol, add_comm]

private theorem complexWhittakerCharacter_reflected {r : ℕ} (a : ℂˣ)
    (u : GeneralLinear.upperUnipotent (r + 1) ℂ) :
    complexWhittakerCharacter a (Whittaker.reflectedUnipotent u).val =
      complexWhittakerCharacter (-a) u.val := by
  unfold complexWhittakerCharacter
  rw [Whittaker.reflectedUnipotent_sum]
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Units.val_neg, mul_neg, neg_mul]

private theorem positionCharacter_map_inv (d : List ComplexCharacterData) (i : ℕ) (z : ℂˣ) :
    complexPositionCharacter (d.map ComplexCharacterData.inv) i z =
      (complexPositionCharacter d i z)⁻¹ := by
  induction d generalizing i with
  | nil => simp [complexPositionCharacter]
  | cons d ds ih =>
    cases i with
    | zero => exact d.inv_character_apply z
    | succ i => exact ih i

private def standardTwist {n : ℕ} {d : List ComplexCharacterData} (hd : d.length = n) :
    complexStandardKFinite n d ≃ₗ[ℂ] complexStandardKFinite n (d.reverse.map ComplexCharacterData.inv) :=
  ComplexTransposeStandardDuality.twistEquiv fun j z => by
    rw [positionCharacter_map_inv, ComplexReverseIntertwinerStrict.complexPositionCharacter_inv]
    congr 1
    simpa only [Fin.rev_rev] using
      congrFun (ComplexReverseIntertwinerStrict.complexPositionCharacter_reverse hd j.rev) z

private def dualIntertwiner {r : ℕ} {d : List ComplexCharacterData} (hd : d.length = r + 1)
    (B : complexStandardKFinite (r + 1) d →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ)) :
    complexStandardKFinite (r + 1) (d.reverse.map ComplexCharacterData.inv) →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
  (twistLin (r + 1)).comp (B.comp (standardTwist hd).symm.toLinearMap)

private theorem isComplexWhittakerIntertwiner_dual {r : ℕ} {d : List ComplexCharacterData}
    (hd : d.length = r + 1) {a : ℂˣ}
    {B : complexStandardKFinite (r + 1) d →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r d a B) :
    IsComplexWhittakerIntertwiner r (d.reverse.map ComplexCharacterData.inv) (-a)
      (dualIntertwiner hd B) := by
  let E := standardTwist hd
  let G := Langlands.GeneralLinear (r + 1) ℂ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f u hu g
    let v : GeneralLinear.upperUnipotent (r + 1) ℂ := ⟨u, hu⟩
    change B (E.symm f) (ComplexReverseTwist.twist (v.val * g)) =
      complexWhittakerCharacter (-a) v.val * B (E.symm f) (ComplexReverseTwist.twist g)
    rw [twist_eq_weylInverseTranspose (v.val * g),
      Whittaker.weylInverseTranspose_left_unipotent, ← twist_eq_weylInverseTranspose,
      hB.1 _ _ (Whittaker.reflectedUnipotent v).2, complexWhittakerCharacter_reflected]
  · intro f
    exact contMDiff_twistLin (hB.2.1 (E.symm f))
  · intro f
    obtain ⟨C, N, h⟩ := hB.2.2.1 (E.symm f)
    refine ⟨C, N, fun g => ?_⟩
    change ‖B (E.symm f) (ComplexReverseTwist.twist g)‖ ≤ C * complexMatrixHeight g ^ N
    simpa only [complexMatrixHeight_twist] using h (ComplexReverseTwist.twist g)
  · intro k f f' hf
    let k₀ := conjK (r + 1) k
    have hf₀ : (E.symm f' : G → ℂ) =
        Whittaker.rightTranslation ℂ G (k₀ : G) (E.symm f) := by
      change twistLin (r + 1) (f' : G → ℂ) =
        Whittaker.rightTranslation ℂ G (k₀ : G) (twistLin (r + 1) (f : G → ℂ))
      rw [hf, rightTranslation_twistLin, show (k₀ : G) = conjAut (k : G) from rfl,
        conjAut_conjAut]
    change twistLin (r + 1) (B (E.symm f')) =
      Whittaker.rightTranslation ℂ G (k : G) (twistLin (r + 1) (B (E.symm f)))
    rw [rightTranslation_twistLin, hB.2.2.2.1 k₀ _ _ hf₀]
    rfl
  · intro X f f' hf
    have hfSmooth : ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ (f : G → ℂ) := f.2.1.1
    have hf₀ : (E.symm f' : G → ℂ) =
        rightDerivative (matrixModel ℂ (r + 1)) (-Xᵀ) (E.symm f) := by
      funext g
      change twistLin (r + 1) (f' : G → ℂ) g =
        rightDerivative (matrixModel ℂ (r + 1)) (-Xᵀ) (twistLin (r + 1) (f : G → ℂ)) g
      rw [hf, ComplexReverseIntertwinerTied.rightDerivative_twistLin hfSmooth]
      simp [twistLin_apply]
    funext g
    change twistLin (r + 1) (B (E.symm f')) g =
      rightDerivative (matrixModel ℂ (r + 1)) X (twistLin (r + 1) (B (E.symm f))) g
    rw [ComplexReverseIntertwinerTied.rightDerivative_twistLin (hB.2.1 (E.symm f)),
      hB.2.2.2.2 (-Xᵀ) _ _ hf₀]
    rfl

/-- The dual of a complex Whittaker-model function belongs to the model for the reversed
inverse characters and the negated additive parameter. -/
theorem complexLocalDualWhittaker_mem {r : ℕ} {d : List ComplexCharacterData}
    (hd : d.length = r + 1) {a : ℂˣ} {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : W ∈ complexWhittakerModel r d a) :
    ArchimedeanLocal.dualFunction (r + 1) W ∈
      complexWhittakerModel r (d.reverse.map ComplexCharacterData.inv) (-a) := by
  let V := complexWhittakerModel r (d.reverse.map ComplexCharacterData.inv) (-a)
  have hle : complexWhittakerModel r d a ≤ V.comap (twistLin (r + 1)) := by
    refine iSup_le fun B => iSup_le fun hB _ hmem => ?_
    obtain ⟨f, rfl⟩ := hmem
    change twistLin (r + 1) (B f) ∈ V
    refine Submodule.mem_iSup_of_mem (dualIntertwiner hd B)
      (Submodule.mem_iSup_of_mem (isComplexWhittakerIntertwiner_dual hd hB)
        ⟨standardTwist hd f, ?_⟩)
    change twistLin (r + 1) (B ((standardTwist hd).symm (standardTwist hd f))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [dualFunction_eq_twistLin]
  exact hle hW

end Langlands.Global.RankinSelbergGlobal
