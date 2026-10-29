import Langlands.Representation.Exponents.OppositeJacquetScalarSubquotient
import Langlands.Representation.Exponents.OppositeJacquetDualToPrimal
import Langlands.Representation.Exponents.TransportedComplexTwistScalarCharacter
import Langlands.Representation.Exponents.GeneralTemperedExponentNecessity
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Representation.Exponents.TemperedOppositeTwistConeStatement
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Classification.MaximalConePolygon

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

private theorem block_constant_cone_of_boundaries {n : ℕ} (E : BlockShape n)
    (V : Fin n → ℝ)
    (hconstant : ∀ x y, blockIndex E x = blockIndex E y → V x = V y)
    (htotal : ∑ a, V a = 0)
    (hboundary : ∀ m : ℕ, 0 ≤ pre V (E.startN m)) :
    IsClosedPositiveRootCone V := by
  refine ⟨htotal, ?_⟩
  intro m _hm hmn
  change 0 ≤ pre V m
  let j := blockIndex E ⟨m, hmn⟩
  obtain ⟨hj1, hj2⟩ := E.blockIndex_spec ⟨m, hmn⟩
  refine pre_nonneg_of_antitone V (a := E.startN j)
    (b := E.startN (j.val + 1)) ?_ (hboundary _) (hboundary _) hj1
    (by rw [E.startN_succ]; exact hj2.le)
  intro x y hx hxy hy
  rw [E.startN_succ] at hy
  have hx' : blockIndex E x = j :=
    (E.blockIndex_eq_iff x j).2 ⟨hx, lt_of_le_of_lt (Fin.le_def.mp hxy) hy⟩
  have hy' : blockIndex E y = j :=
    (E.blockIndex_eq_iff y j).2 ⟨le_trans hx (Fin.le_def.mp hxy), hy⟩
  exact (hconstant y x (hy'.trans hx'.symm)).le

private theorem cone_pre_nonneg {n : ℕ} {V : Fin n → ℝ}
    (hV : IsClosedPositiveRootCone V) (m : ℕ) : 0 ≤ pre V m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pre]
  · by_cases hmn : m < n
    · exact hV.2 m hm hmn
    · have hnm : n ≤ m := Nat.le_of_not_gt hmn
      unfold pre
      rw [Finset.filter_true_of_mem (fun a _ => lt_of_lt_of_le a.isLt hnm)]
      exact hV.1.ge

private theorem diagonal_cone_of_weighted_block_cone {n : ℕ} (E : BlockShape n)
    (f : Fin E.length → ℝ)
    (hf : IsClosedPositiveRootCone (fun i => (E.size i : ℝ) * f i)) :
    IsClosedPositiveRootCone (fun a => f (blockIndex E a)) := by
  classical
  apply block_constant_cone_of_boundaries E
  · intro x y hxy
    rw [hxy]
  · calc
      _ = ∑ k, (E.size k : ℝ) * f k := by
        simpa using E.sum_blockIndex f (fun _ => True)
      _ = 0 := hf.1
  · intro m
    rw [pre_blockIndex_eq E f (E.startN m) (fun k => (k : ℕ) < m)
      (fun a => E.lt_startN_iff a m)]
    exact cone_pre_nonneg hf m

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
  have hdiagonal := TemperedOppositeTwistCone.diagonal_cone_of_weighted_block_cone E
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
