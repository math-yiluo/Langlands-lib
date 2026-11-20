import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Archimedean.RealCharacterReverseKernel
import Langlands.Representation.Whittaker.DualTransform

/-! # The actual Weyl inverse-transpose on real uniform Whittaker coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean Langlands.Whittaker
open Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealUniformWhittakerDual

open RealReverseTwist RealStrictCharacterLanglandsQuotient

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "KF" => realStandardKFinite (r + 1)

private theorem twist_eq_weylInverseTranspose {n : ℕ} (g : Langlands.GeneralLinear n ℝ) :
    RealReverseTwist.twist g = weylInverseTranspose n ℝ g := by
  have hw : w0GL n = weylLong n ℝ := by
    apply Units.ext
    ext i j
    simp only [w0GL_val, w0Mat_apply, weylLong_entry, eq_comm]
  rw [RealReverseTwist.twist, weylInverseTranspose_apply, hw]
  rfl

private theorem dualFunction_eq_twistLin {n : ℕ} (W : Langlands.GeneralLinear n ℝ → ℂ) :
    ArchimedeanLocal.dualFunction n W = twistLin n W := by
  funext g
  exact congrArg W (twist_eq_weylInverseTranspose g).symm

private theorem height_twist {n : ℕ} (g : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight (RealReverseTwist.twist g) = realMatrixHeight g := by
  have hInv (i j : Fin n) : ((weylInverseTranspose n ℝ g)⁻¹ : Langlands.GeneralLinear n ℝ) i j =
      g j.rev i := by
    rw [weylInverseTranspose_apply, _root_.mul_inv_rev, weylLong_inv, ← map_inv,
      mul_weylLong_entry, inverseTranspose_entry, inv_inv]
  have hRow (A : Matrix (Fin n) (Fin n) ℝ) :
      (∑ i : Fin n, ∑ j : Fin n, ‖A j i.rev‖ ^ 2) = ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 :=
    (Equiv.sum_comp Fin.revPerm (fun i => ∑ j : Fin n, ‖A j i‖ ^ 2)).trans Finset.sum_comm
  have hCol (A : Matrix (Fin n) (Fin n) ℝ) :
      (∑ i : Fin n, ∑ j : Fin n, ‖A j.rev i‖ ^ 2) = ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
    simp_rw [show ∀ i : Fin n, (∑ j : Fin n, ‖A j.rev i‖ ^ 2) = ∑ j : Fin n, ‖A j i‖ ^ 2
      from fun i => Equiv.sum_comp Fin.revPerm (fun j => ‖A j i‖ ^ 2)]
    exact Finset.sum_comm
  rw [twist_eq_weylInverseTranspose]
  simp only [realMatrixHeight, Finset.sum_add_distrib, weylInverseTranspose_entry, hInv, hRow, hCol, add_comm]

private def transportedIntertwiner {ds es : List RealBlock} (E : KF es ≃ₗ[ℂ] KF ds)
    (B : KF ds →ₗ[ℂ] (G → ℂ)) : KF es →ₗ[ℂ] (G → ℂ) :=
  (twistLin (r + 1)).comp (B.comp E.toLinearMap)

/-- Transport under a source equivalence with the compact and Lie actions of inverse transpose. -/
theorem dualFunction_mem_of_equiv {ds es : List RealBlock} (E : KF es ≃ₗ[ℂ] KF ds)
    (hK : ∀ (k : Matrix.unitaryGroup (Fin (r + 1)) ℝ) (f : KF es),
      E (realStandardRep (r + 1) es k f) = realStandardRep (r + 1) ds k (E f))
    (hLie : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (f : KF es),
      E (realStandardLie (r + 1) es (1 ⊗ₜ[ℝ] X) f) =
        realStandardLie (r + 1) ds (1 ⊗ₜ[ℝ] (-X.transpose)) (E f))
    (a : ℝˣ) {W : G → ℂ} (hW : W ∈ realUniformWhittakerModel r ds a) :
    ArchimedeanLocal.dualFunction (r + 1) W ∈ realUniformWhittakerModel r es (-a) := by
  have hC (B : KF ds →ₗ[ℂ] (G → ℂ)) (hB : IsRealUniformWhittakerIntertwiner r ds a B) :
      IsRealUniformWhittakerIntertwiner r es (-a) (transportedIntertwiner E B) := by
    obtain ⟨⟨hN, hSmooth, hGrowth, hBk, hBx⟩, N, hBound⟩ := hB
    have hU (f : KF es) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G,
        ‖transportedIntertwiner E B f g‖ ≤ C * realMatrixHeight g ^ N := by
      obtain ⟨C, hC, hC'⟩ := hBound (E f)
      refine ⟨C, hC, fun g => ?_⟩
      change ‖B (E f) (RealReverseTwist.twist g)‖ ≤ C * realMatrixHeight g ^ N
      simpa only [height_twist] using hC' (RealReverseTwist.twist g)
    refine ⟨⟨?_, fun f => contMDiff_twistLin (hSmooth (E f)), ?_, ?_, ?_⟩, N, hU⟩
    · intro f u hu g
      let v : GeneralLinear.upperUnipotent (r + 1) ℝ := ⟨u, hu⟩
      change B (E f) (RealReverseTwist.twist (v.val * g)) = realWhittakerCharacter (-a) v.val * B (E f) (RealReverseTwist.twist g)
      rw [twist_eq_weylInverseTranspose (v.val * g), weylInverseTranspose_left_unipotent,
        ← twist_eq_weylInverseTranspose, hN _ _ (reflectedUnipotent v).property,
        Langlands.Global.RankinSelbergGlobal.RealUnequalPairConvergence.realWhittakerCharacter_reflected]
    · intro f
      obtain ⟨C, _, h⟩ := hU f
      exact ⟨C, N, h⟩
    · intro k f f' hf'
      let κ : Matrix.unitaryGroup (Fin (r + 1)) ℝ := ⟨k.val.val, k.property⟩
      have hk : Unitary.toUnits κ = k.val := Units.ext rfl
      have hf'Eq : f' = realStandardRep (r + 1) es κ f := by
        apply Subtype.ext
        rw [realStandardRep_apply_coe, hk]
        exact hf'
      have hf₀ : (E f' : G → ℂ) = rightTranslation ℂ G k.val (E f : G → ℂ) := by
        rw [hf'Eq, hK, realStandardRep_apply_coe, hk]
      change twistLin (r + 1) (B (E f')) = rightTranslation ℂ G k.val (twistLin (r + 1) (B (E f)))
      rw [rightTranslation_twistLin _ k.property, hBk k _ _ hf₀]
    · intro X f f' hf'
      have hf'Eq : f' = realStandardLie (r + 1) es (1 ⊗ₜ[ℝ] X) f := by
        apply Subtype.ext
        rw [realStandardLie_one_tmul_apply_coe]
        exact hf'
      have hf₀ : (E f' : G → ℂ) = rightDerivative (matrixModel ℝ (r + 1)) (-X.transpose) (E f : G → ℂ) := by
        rw [hf'Eq, hLie, realStandardLie_one_tmul_apply_coe]
      change twistLin (r + 1) (B (E f')) = rightDerivative (matrixModel ℝ (r + 1)) X (twistLin (r + 1) (B (E f)))
      rw [rightDerivative_twistLin (hSmooth (E f)), hBx (-X.transpose) _ _ hf₀]
  have hLe : realUniformWhittakerModel r ds a ≤
      (realUniformWhittakerModel r es (-a)).comap (twistLin (r + 1)) := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    change twistLin (r + 1) (B f) ∈ realUniformWhittakerModel r es (-a)
    have hrange : LinearMap.range (transportedIntertwiner E B) ≤ realUniformWhittakerModel r es (-a) :=
      le_iSup_of_le _ (le_iSup_of_le (hC B hB) le_rfl)
    exact hrange ⟨E.symm f, by simp [transportedIntertwiner]⟩
  rw [dualFunction_eq_twistLin]
  exact hLe hW

/-- The reversed inverse list of a real character principal series. -/
def dualCharacterBlocks (cs : List RealCharacterData) : List RealBlock :=
  (cs.reverse.map RealCharacterData.inverse).map RealBlock.character

private theorem positionCharacter_map_inverse : ∀ (cs : List RealCharacterData) (l : ℕ) (z : ℝˣ),
    realPositionCharacter ((cs.map RealCharacterData.inverse).map RealBlock.character) l z =
      realPositionCharacter (cs.map RealBlock.character) l z⁻¹
  | [], _, _ => rfl
  | c :: cs, 0, z => by
    change (c.inverse.character z : ℂ) = (c.character z⁻¹ : ℂ)
    simp only [RealCharacterData.inverse_character, map_inv]
    rfl
  | c :: cs, l + 1, z => positionCharacter_map_inverse cs l z

private theorem positionCharacter_dual {n : ℕ} {cs : List RealCharacterData} (hn : cs.length = n)
    (i : Fin n) (z : ℝˣ) : realPositionCharacter (dualCharacterBlocks cs) i z =
      realPositionCharacter (cs.map RealBlock.character) i.rev z⁻¹ := by
  rw [dualCharacterBlocks, positionCharacter_map_inverse, List.map_reverse]
  let ds := cs.map RealBlock.character
  have hd : ds.length = n := by simpa only [ds, List.length_map] using hn
  have hDs : IsCharacterList ds := by
    intro d hd
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hd
    exact ⟨c, rfl⟩
  change realPositionCharacter ds.reverse i z⁻¹ = realPositionCharacter ds i.rev z⁻¹
  rw [RealCharacterReverseKernel.realPositionCharacter_reverse hDs _ (by rw [hd]; exact i.isLt), hd, Fin.val_rev]
  rw [show n - 1 - i.val = n - (i.val + 1) by omega]

private theorem standardKFinite_map_character (n : ℕ) (cs : List RealCharacterData) :
    realStandardKFinite n (cs.map RealBlock.character) =
      kFiniteFunctions (principalSeries ℝ n (realPositionCharacter (cs.map RealBlock.character)))
        (unitaryCompact ℝ n) := by
  unfold realStandardKFinite
  congr 1
  ext f
  rw [mem_realStandardModule_iff]
  refine ⟨And.left, fun h => ⟨h, fun p d hd => ?_⟩⟩
  rw [RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
  cases hd

private def characterTwist {cs : List RealCharacterData} (hn : cs.length = r + 1) :
    KF (dualCharacterBlocks cs) ≃ₗ[ℂ] KF (cs.map RealBlock.character) where
  toFun f := ⟨twistLin (r + 1) f.val, by
    rw [standardKFinite_map_character]
    have hf : f.val ∈ kFiniteFunctions (principalSeries ℝ (r + 1) (realPositionCharacter (dualCharacterBlocks cs)))
        (unitaryCompact ℝ (r + 1)) := ⟨f.2.1.1, f.2.2⟩
    apply twistLin_mem_kFiniteFunctions _ hf
    intro i z
    rw [positionCharacter_dual hn i.rev z⁻¹, Fin.rev_rev, inv_inv]⟩
  invFun f := ⟨twistLin (r + 1) f.val, by
    unfold dualCharacterBlocks
    rw [standardKFinite_map_character]
    exact twistLin_mem_kFiniteFunctions (positionCharacter_dual hn) ⟨f.2.1.1, f.2.2⟩⟩
  left_inv f := Subtype.ext (twistLin_twistLin f.val)
  right_inv f := Subtype.ext (twistLin_twistLin f.val)
  map_add' f f' := Subtype.ext (map_add (twistLin (r + 1)) f.val f'.val)
  map_smul' z f := Subtype.ext (map_smul (twistLin (r + 1)) z f.val)

/-- On the actual real uniform coefficient model of a character list, the
Weyl inverse-transpose gives the opposite-sign model of the reversed inverse list. -/
def RealUniformWhittakerCharacterDualStatement : Prop :=
  ∀ (r : ℕ) (cs : List RealCharacterData), cs.length = r + 1 →
    ∀ (a : ℝˣ) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      W ∈ realUniformWhittakerModel r (cs.map RealBlock.character) a →
      ArchimedeanLocal.dualFunction (r + 1) W ∈ realUniformWhittakerModel r (dualCharacterBlocks cs) (-a)

theorem realUniformWhittakerCharacterDual : RealUniformWhittakerCharacterDualStatement := by
  intro r cs hn a W hW
  apply dualFunction_mem_of_equiv (characterTwist hn) _ _ a hW
  · intro k f
    apply Subtype.ext
    change twistLin (r + 1) (realStandardRep (r + 1) _ k f).val =
      (realStandardRep (r + 1) _ k (characterTwist hn f)).val
    rw [realStandardRep_apply_coe, realStandardRep_apply_coe]
    exact (rightTranslation_twistLin f.val (show Unitary.toUnits k ∈ unitaryCompact ℝ (r + 1)
      from k.property)).symm
  · intro X f
    apply Subtype.ext
    change twistLin (r + 1) (realStandardLie (r + 1) _ (1 ⊗ₜ[ℝ] X) f).val =
      (realStandardLie (r + 1) _ (1 ⊗ₜ[ℝ] (-X.transpose)) (characterTwist hn f)).val
    rw [realStandardLie_one_tmul_apply_coe, realStandardLie_one_tmul_apply_coe]
    change twistLin (r + 1) (rightDerivative (matrixModel ℝ (r + 1)) X f.val) =
      rightDerivative (matrixModel ℝ (r + 1)) (-X.transpose) (twistLin (r + 1) f.val)
    rw [rightDerivative_twistLin f.2.1.1.1, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]

end RealUniformWhittakerDual
end Langlands.Global.RankinSelbergGlobal
