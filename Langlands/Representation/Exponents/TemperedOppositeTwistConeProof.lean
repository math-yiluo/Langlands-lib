import Langlands.Representation.Exponents.OppositeJacquetScalarSubquotient
import Langlands.Representation.Exponents.OppositeJacquetDualToPrimal
import Langlands.Representation.Exponents.TransportedComplexTwistScalarCharacter
import Langlands.Representation.Exponents.GeneralTemperedExponentNecessity
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Representation.Exponents.TemperedOppositeTwistConeStatement
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Exponents.WeightedBlockCone

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear Geometric CuspidalSupport Exponents MaximalConePolygon

universe uF uV uM

namespace TemperedOppositeTwistCone

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Analytic temperedness bounds opposite exponents on decreasing tuples. -/
theorem oppositeBound_of_tempered
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (A : Rep.{uM} ℂ (GeneralLinear n F.Carrier))
    (hA : T.IsTempered A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    ∀ a : Fin B.length → F.Carrierˣ,
      Antitone (fun i => T.normalizedAbs (a i : F.Carrier)) →
      ‖(χ a : ℂ)‖ ≤ 1 := by
  have hgen := oppositeJacquetDualToPrimal T B A hA.isAdmissible χ hχ
  have hexp := ScalarLayer.isJacquetExponent_reverse T B A hχ.1 hgen
  intro a ha
  have h := GeneralTemperedExponentNecessity.upperBound T hn A.ρ hA B.reverse _ hexp (a ∘ Fin.rev)
    (fun i j hij => ha (Fin.rev_le_rev.mpr hij))
  have heq : (a ∘ Fin.rev) ∘ Fin.rev = a := by
    funext i
    simp
  change ‖(χ ((a ∘ Fin.rev) ∘ Fin.rev) : ℂ)‖ ≤ 1 at h
  rwa [heq] at h

private theorem normalizedAbs_inv (a : F.Carrierˣ) :
    T.normalizedAbs ((a⁻¹ : F.Carrierˣ) : F.Carrier) =
      (T.normalizedAbs (a : F.Carrier))⁻¹ := by
  change (T.normalizedAbsHom ((a⁻¹ : F.Carrierˣ) : F.Carrier) : ℝ) = _
  simp only [Units.val_inv_eq_inv_val, map_inv₀, NNReal.coe_inv,
    PadicField.TopologicalData.normalizedAbsHom_coe]

/-- A negative real part bounded on the opposite chamber gives the positive cone. -/
theorem cone_of_opposite_bound {r : ℕ}
    (χ : (Fin r → F.Carrierˣ) →* ℂˣ) (s : Fin r → ℝ)
    (hs : T.IsRealPartOf χ (fun i => -s i))
    (hbound : ∀ a : Fin r → F.Carrierˣ,
      Antitone (fun i => T.normalizedAbs (a i : F.Carrier)) → ‖(χ a : ℂ)‖ ≤ 1) :
    IsClosedPositiveRootCone s := by
  have hs' : T.IsRealPartOf χ⁻¹ s := by
    intro a
    change ‖(((χ a)⁻¹ : ℂˣ) : ℂ)‖ = _
    simp only [Units.val_inv_eq_inv_val, norm_inv]
    rw [hs a]
    have hneg (i : Fin r) : T.normalizedAbs (a i : F.Carrier) ^ (-s i) =
        (T.normalizedAbs (a i : F.Carrier) ^ s i)⁻¹ :=
      Real.rpow_neg (T.normalizedAbs_nonneg _) _
    simp only [hneg, Finset.prod_inv_distrib, inv_inv]
  apply hs'.isClosedPositiveRootCone_iff.mpr
  constructor
  · intro c
    have hle := hbound (fun _ => c) (fun _ _ _ => le_rfl)
    have hinv := hbound (fun _ => c⁻¹) (fun _ _ _ => le_rfl)
    have heq : (fun _ : Fin r => c⁻¹) = (fun _ : Fin r => c)⁻¹ := rfl
    rw [heq, map_inv, Units.val_inv_eq_inv_val, norm_inv] at hinv
    have hpos : 0 < ‖(χ (fun _ => c) : ℂ)‖ :=
      norm_pos_iff.mpr (χ _).ne_zero
    have hn := le_antisymm hle ((inv_le_one₀ hpos).mp hinv)
    change ‖(((χ (fun _ => c))⁻¹ : ℂˣ) : ℂ)‖ = 1
    simp only [Units.val_inv_eq_inv_val, norm_inv, hn, inv_one]
  · intro a ha
    have hanti : Antitone (fun i => T.normalizedAbs (a⁻¹ i : F.Carrier)) := by
      intro i j hij
      change T.normalizedAbs (((a j)⁻¹ : F.Carrierˣ) : F.Carrier) ≤
        T.normalizedAbs (((a i)⁻¹ : F.Carrierˣ) : F.Carrier)
      rw [normalizedAbs_inv, normalizedAbs_inv]
      exact inv_le_inv₀ (T.normalizedAbs_pos (a j).ne_zero)
        (T.normalizedAbs_pos (a i).ne_zero) |>.mpr (ha hij)
    have h := hbound a⁻¹ hanti
    simpa only [MonoidHom.inv_apply, map_inv] using h


end TemperedOppositeTwistCone

/-- An actual transported opposite Jacquet occurrence in a general
analytically tempered source forces the full diagonal positive cone. -/
theorem glTemperedOppositeTwistCone :
    GLTemperedOppositeTwistConeStatement.{uF,uV,uM} := by
  intro p _ F T
  let := T.topology
  intro n hn C E w hw ω hi ha hu v b A hA hocc
  obtain ⟨χ, hopen, hscalar, hreal⟩ :=
    transportedComplexTwistScalarCharacter T C E w hw ω hi ha hu v b
  have hχ := isDualJacquetExponent_of_scalar_oppositeClassExponent T E A hA.isAdmissible _ χ hocc hscalar
  have hbound := TemperedOppositeTwistCone.oppositeBound_of_tempered T hn E A hA χ hχ
  have hcone := TemperedOppositeTwistCone.cone_of_opposite_bound T χ
    (fun j => (E.size j : ℝ) * v ((blockEquiv hw).symm j)) hreal hbound
  have hdiagonal := Exponents.diagonal_cone_of_weighted_block_cone E
    (fun j => v ((blockEquiv hw).symm j)) hcone
  have heq : (fun a => v (blockIndex C (w.symm a))) =
      (fun a => v ((blockEquiv hw).symm (blockIndex E a))) := by
    funext a
    congr 1
    apply (blockEquiv hw).injective
    change blockMap C E w (blockIndex C (w.symm a)) = _
    rw [← blockIndex_apply_eq_blockMap hw, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  rwa [heq]

end Langlands
