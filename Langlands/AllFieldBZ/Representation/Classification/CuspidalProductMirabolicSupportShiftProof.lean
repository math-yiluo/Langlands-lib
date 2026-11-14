import Langlands.AllFieldBZ.Representation.Classification.CuspidalProductContragredient
import Langlands.AllFieldBZ.Representation.Classification.CuspidalProductDerivativeQuotientSupport
import Langlands.AllFieldBZ.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement
import Langlands.AllFieldBZ.Representation.Classification.MirabolicDerivativeContragredient
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof

/-!
# All-field port of `Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Classification.CuspidalProductMirabolicSupportShiftProof
open Langlands.Classification.CuspidalProductMirabolicSupportShiftProof hiding eq_zero_of_isSupercuspidalSupport le_of_derivative_hom
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement PartialDerivativeJacquetComparisonStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl partialDerivative partialDerivativeJacquetComparison partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero positiveTwoBlockNormalizedJacquet
open Langlands.AllFieldBZ.Derivative
open Langlands.Classification.CuspidalProductContragredient hiding classContragredient_realPowerTwist cuspidalProductInduced_dualDatum cuspidalProductInduced_twistedDualData determinantPowerCharacter_leviEmbedding determinantPowerCharacter_parabolic dualClass dualClass_def dualDatum dualDatum_cls dualDatum_dualDatum dualDatum_rank dualDatum_twist dualRep dualRep_obj dualRep_represents isCuspidalConstituent_contragredient isSupercuspidalSupport_contragredient nonempty_contragredient_cuspidalProductIso nonempty_contragredient_productEquiv nonempty_twist_productEquiv nonempty_twistedDual_cuspidalProductEquiv ofFn_twistedDualData twist_le_of_dual_le twistedDualData twistedDualRep twistedDualRep_represents
open Langlands.AllFieldBZ.Classification.CuspidalProductContragredient
open Langlands.Classification.MirabolicDerivativeContragredient hiding exists_derivative_hom_contragredient exists_determinant_pairing mirabolicDerivativeOfOrder_restriction mirabolicRankCast_restriction
open Langlands.AllFieldBZ.Classification.MirabolicDerivativeContragredient
universe uF uV

variable {F : LocalFieldPackage.{uF}} {T : F.TopologicalData}

section Support
/-- A representation of `GL_0` has only the empty supercuspidal support. -/
theorem eq_zero_of_isSupercuspidalSupport {n : ℕ} (hn : n = 0)
    {σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset T.CuspidalDatum.{uV, uF}} (hs : T.IsSupercuspidalSupport σ s) : s = 0 := by
  obtain ⟨l, ρ, rfl, h, -⟩ := hs
  cases l with
  | zero => rfl
  | succ l =>
    have := Finset.single_le_sum (f := fun i => (ρ i).rank) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (0 : Fin (l + 1)))
    have := (ρ 0).rank_pos
    omega

/-- Lemma 4.7(a), quotient form, for supports: if `0 < k < n` and an irreducible `τ`
receives a nonzero morphism from the order-`k` derivative of a cuspidal product
`ρ_1 × ⋯ × ρ_r`, then every supercuspidal support of `τ` is contained in
`ρ_1 + ⋯ + ρ_r`. -/
theorem le_of_derivative_hom
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {r : ℕ} (ρ : Fin r → T.CuspidalDatum.{uV, uF}) {n : ℕ} (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i)) {k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (hkn : k < n)
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (q : letI := T.topology
      (Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ n k hk).obj (T.cuspidalProductInduced ρ h A) ⟶ τ)
    (hq : letI := T.topology; SmoothRep.hom q ≠ 0)
    {s : Multiset T.CuspidalDatum.{uV, uF}} (hs : T.IsSupercuspidalSupport τ s) :
    s ≤ (List.ofFn ρ : Multiset T.CuspidalDatum.{uV, uF}) := by
  let := T.topology
  obtain ⟨l, ρ'', hcon, hle⟩ :=
    CuspidalProductDerivativeQuotientSupport.derivative_quotient_support.{uF, uV} T ψ hk hk0
      hkn ρ h A hA τ hτ (SmoothRep.hom q).toLinearMap
      (fun hz => hq (by ext v; exact LinearMap.congr_fun hz v))
      (fun g v => LinearMap.congr_fun ((SmoothRep.hom q).isIntertwining' g) v)
  have huniq := glSupercuspidalSupportUniqueness.{uV, uF} F T (n - k) (by omega) τ hτ
    s (List.ofFn ρ'') hs ⟨l, ρ'', rfl, hcon⟩
  rw [huniq]
  exact hle

end Support
end Langlands.AllFieldBZ.Classification.CuspidalProductMirabolicSupportShiftProof
namespace Langlands.AllFieldBZ.Classification
open Langlands.Classification hiding CuspidalProductMirabolicSupportShift cuspidalProductMirabolicSupportShift
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous MirabolicDerivativeDetection MirabolicHighestDerivativePairingStatement PartialDerivativeJacquetComparisonStatement generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicHighestDerivativePairing mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl partialDerivative partialDerivativeJacquetComparison partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero positiveTwoBlockNormalizedJacquet
open Langlands.AllFieldBZ.Derivative
open Langlands.Classification.CuspidalProductContragredient hiding classContragredient_realPowerTwist cuspidalProductInduced_dualDatum cuspidalProductInduced_twistedDualData determinantPowerCharacter_leviEmbedding determinantPowerCharacter_parabolic dualClass dualClass_def dualDatum dualDatum_cls dualDatum_dualDatum dualDatum_rank dualDatum_twist dualRep dualRep_obj dualRep_represents isCuspidalConstituent_contragredient isSupercuspidalSupport_contragredient nonempty_contragredient_cuspidalProductIso nonempty_contragredient_productEquiv nonempty_twist_productEquiv nonempty_twistedDual_cuspidalProductEquiv ofFn_twistedDualData twist_le_of_dual_le twistedDualData twistedDualRep twistedDualRep_represents
open Langlands.AllFieldBZ.Classification.CuspidalProductContragredient
open Langlands.Classification.MirabolicDerivativeContragredient hiding exists_derivative_hom_contragredient exists_determinant_pairing mirabolicDerivativeOfOrder_restriction mirabolicRankCast_restriction
open Langlands.AllFieldBZ.Classification.MirabolicDerivativeContragredient
open Langlands.Classification.CuspidalProductMirabolicSupportShiftProof hiding eq_zero_of_isSupercuspidalSupport le_of_derivative_hom
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- BZ77 Lemma 4.7(b), mirabolic form: if `W ⊆ (ρ_1 × ⋯ × ρ_r)|P` has highest
derivative `W^(k)`, `k > 0`, then `ν · supp σ ≤ ρ_1 + ⋯ + ρ_r` for every irreducible
subrepresentation `σ` of `W^(k)`. -/
theorem cuspidalProductMirabolicSupportShift :
    CuspidalProductMirabolicSupportShift.{uF, uV} F T := by
  let := T.topology
  intro ψ N r ρ h A hA W f hf k hk hlevel σ hσ s hs
  rcases Nat.lt_or_ge k (N + 1) with hkn | hkn
  · let := T.generalLinearTopologicalGroup (N + 1)
    let := T.generalLinearTopologicalGroup (N + 1 - k)
    obtain ⟨Φ⟩ := Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_twistedDual_cuspidalProductEquiv 1 ρ h A
    obtain ⟨β, hβ⟩ := Langlands.AllFieldBZ.Classification.MirabolicDerivativeContragredient.exists_determinant_pairing (T.cuspidalProductInduced ρ h A)
      (T.cuspidalProductInduced (Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualData 1 ρ) h (fun i => Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualRep T 1 (A i)))
      Φ W f hf
    obtain ⟨q, hq⟩ := Langlands.AllFieldBZ.Classification.MirabolicDerivativeContragredient.exists_derivative_hom_contragredient ψ _ W β hβ k hk hlevel σ hσ
    have hadm : σ.IsAdmissible :=
      (CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T _ σ hσ.1).1
    have hirr : σ.contragredient.IsIrreducible :=
      (SmoothRep.isIrreducible_contragredient_iff (Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T _) σ hadm).mpr hσ.1
    apply Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twist_le_of_dual_le ρ s
    exact Langlands.AllFieldBZ.Classification.CuspidalProductMirabolicSupportShiftProof.le_of_derivative_hom ψ (Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualData 1 ρ) h (fun i => Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualRep T 1 (A i))
      (fun i => Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualRep_represents 1 (hA i)) hk.2 hk.1 hkn σ.contragredient hirr q hq
      (Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.isSupercuspidalSupport_contragredient hs)
  · obtain rfl : k = N + 1 := le_antisymm hk.2 hkn
    rw [Langlands.AllFieldBZ.Classification.CuspidalProductMirabolicSupportShiftProof.eq_zero_of_isSupercuspidalSupport (Nat.sub_self (N + 1)) hs]
    simp

end Langlands.AllFieldBZ.Classification
