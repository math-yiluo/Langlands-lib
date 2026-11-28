import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicSiegelChamberGeometryStatement
import Langlands.Global.RelativeRootChamberLog
import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionProof
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor

/-! # Lower Iwasawa height along a standard parabolic cone -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj NNReal TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- A lower bound for the simple-root logs gives a lower bound for each positive root. -/
private theorem exists_positiveRoot_log_lower_bound
    {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {β : characterLattice T} (hβ : β ∈ positiveRelativeRoots i ν) :
    ∃ n : ℕ, ∀ (logValue : characterLattice T →+ ℝ) (lo : ℝ),
      (∀ α ∈ simpleRelativeRoots i ν, lo ≤ logValue α) → (n : ℝ) * lo ≤ logValue β := by
  have h := positiveRelativeRoots_subset_closure_simpleRelativeRoots i ν hβ
  clear hβ
  induction h using AddSubmonoid.closure_induction with
  | mem α hα => exact ⟨1, fun logValue lo hlo => by simpa only [Nat.cast_one, one_mul] using hlo α hα⟩
  | zero => exact ⟨0, fun logValue lo _ => by simp⟩
  | add α β _ _ hα hβ =>
    obtain ⟨m, hm⟩ := hα
    obtain ⟨n, hn⟩ := hβ
    refine ⟨m + n, fun logValue lo hlo => ?_⟩
    rw [Nat.cast_add, add_mul, map_add]
    exact add_le_add (hm logValue lo hlo) (hn logValue lo hlo)

set_option maxHeartbeats 1000000 in
/-- The determinant on the standard parabolic radical supplies the height functional
with a positive slope on the cone. -/
theorem standardParabolicConeHeight : StandardParabolicConeHeightStatement := by
  classical
  intro F _ _ G _ _ _ hG K T i ν T₀ j hsetup J hJ hProper hK δ hδ t Ω hΩ
  obtain ⟨α, hα, hαJ⟩ := hProper
  obtain ⟨hi, hν, _, _, _, _, _, _, Z, zc, hZc, _⟩ := hsetup
  have hT := hi.isSplitSubtorus.1
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hDynamic⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  let P := Standard.parabolicScheme i ν J
  let p := Standard.parabolicHom i ν J
  let : IsAffineHom P.X.hom := (Standard.isClosedSubgroup_parabolicHom i ν J).isAffineHom
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  let : IsClosedImmersion p.hom.hom.left := Standard.isClosedSubgroup_parabolicHom i ν J
  let M := Standard.leviScheme i ν J
  let l := Standard.leviHom i ν J
  let tM := standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
  let ψ := CommGroupScheme.groupHom ζ ≫ i
  obtain ⟨hPface, hMface, _⟩ := hDynamic ζ hζ
  have hP : (Dynamic.parabolic ψ).IsRepresentedBy p := by
    rw [← hPface]
    exact Standard.isRepresentedBy_parabolicHom i ν J
  have hM : (Dynamic.centralizer ψ).IsRepresentedBy l := by
    rw [← hMface]
    exact Standard.isRepresentedBy_leviHom i ν J
  let U := Dynamic.Affine.unipotentScheme ψ
  let : IsAffineHom U.X.hom := (Dynamic.Affine.isClosedSubgroup_unipotentHom ψ).isAffineHom
  let : LocallyOfFiniteType U.X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom ψ).locallyOfFiniteType
  let : IsAffineHom M.X.hom := (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  let c := Lie.finiteCoordinates U
  let χ := Dynamic.adjointDeterminantCharacter hP hU c
  let tP := tM ≫ Dynamic.centralizerToParabolic hP hM
  have htM : tM ≫ l = i := standardLeviTorusFactor_comp i ν J _
  have htP : tP ≫ p = i := by
    rw [show tP = tM ≫ Dynamic.centralizerToParabolic hP hM from rfl,
      Category.assoc, Dynamic.centralizerToParabolic_comp, htM]
  have hRestrict : characterRestrict tP χ = positiveWeightCharacter i ζ := by
    rw [show tP = tM ≫ Dynamic.centralizerToParabolic hP hM from rfl,
      characterRestrict_comp, AddMonoidHom.comp_apply,
      Dynamic.adjointDeterminantCentralizerRestriction ψ hP hM hU c]
    exact characterRestrict_centralizerAdjointDeterminant hT i ζ hM hU tM htM c
  let m (β : characterLattice T) : ℕ :=
    if 0 < latticePairing T β ζ then Module.finrank F (weightSpace i β) else 0
  have hs : (Function.support m).Finite :=
    (hT.finite_weightSupport i).subset fun β hβ hbot => by
      apply hβ
      simp [m, hbot]
  let s := hs.toFinset
  have hPositive (β : characterLattice T) (hβ : β ∈ s) : β ∈ positiveRelativeRoots i ν := by
    have hm : m β ≠ 0 := hs.mem_toFinset.mp hβ
    have hζpos : 0 < latticePairing T β ζ := by
      by_contra h
      exact hm (ite_eq_right h)
    have hroot : β ∈ relativeRoots i := by
      refine ⟨?_, ?_⟩
      · rintro rfl
        simp at hζpos
      · intro hbot
        exact hm (by simp [m, hbot])
    refine ⟨hroot, ?_⟩
    rcases lt_or_gt_of_ne (hν β hroot) with hneg | hpos
    · have hNegRoot : -β ∈ relativeRoots i := relativeRootNegation F G hG T i hi β hroot
      have hNegPos : -β ∈ positiveRelativeRoots i ν := ⟨hNegRoot, by
        rw [map_neg, LinearMap.neg_apply]
        omega⟩
      have hbad := hζ.pairing_nonneg_of_positive i ν hNegPos
      rw [map_neg, LinearMap.neg_apply] at hbad
      omega
    · exact hpos
  have hmα : 0 < m α := by
    let : FiniteDimensional F (Additive (G.lieKernel F)) := Lie.finiteDimensional_lieKernel G
    have hmα' : 0 < Module.finrank F (weightSpace i α) :=
      Nat.pos_of_ne_zero (fun h => hα.1.1.2 (Submodule.finrank_eq_zero.mp h))
    rw [show m α = _ from ite_eq_left (hζ.2.2 α hα hαJ)]
    exact hmα'
  have hαs : α ∈ s := hs.mem_toFinset.mpr hmα.ne'
  have hsum : characterRestrict tP χ =
      ∑ β ∈ s, m β • (rationalCharacters.equivCharacterLattice T).symm β := by
    rw [hRestrict]
    change (∑ᶠ β, m β • (rationalCharacters.equivCharacterLattice T).symm β) = _
    apply finsum_eq_sum_of_support_subset
    intro β hβ
    exact hs.mem_toFinset.mpr (fun hb => hβ (by simp only [hb, zero_smul]))
  have htLog (x : AdelicGroupPoints F T.toGrp) :
      characterLog F P (map F T.toGrp P tP x) χ =
        ∑ β ∈ s, (m β : ℝ) * logNormHom F T x β := by
    rw [characterLog_map]
    let logEval : rationalCharacters T.toGrp →+ ℝ := characterLog F T.toGrp x
    change logEval (characterRestrict tP χ) = _
    rw [hsum, map_sum]
    simp only [map_nsmul, nsmul_eq_mul]
    rfl
  have hlower (β : characterLattice T) : ∃ n : ℕ,
      ∀ (logValue : characterLattice T →+ ℝ) (lo : ℝ),
        (∀ root ∈ simpleRelativeRoots i ν, lo ≤ logValue root) →
          β ∈ s → (n : ℝ) * lo ≤ logValue β := by
    by_cases hβ : β ∈ s
    · obtain ⟨n, hn⟩ := exists_positiveRoot_log_lower_bound i ν (hPositive β hβ)
      exact ⟨n, fun logValue lo hlo _ => hn logValue lo hlo⟩
    · exact ⟨0, fun _ _ _ h => (hβ h).elim⟩
  choose n hn using hlower
  let lt := Real.log ((t : ℝ≥0) : ℝ)
  let L := ∑ β ∈ s.erase α, ((m β : ℝ) * (n β : ℝ)) * lt
  obtain ⟨B, hB⟩ :=
    (hΩ.image ((continuous_dualEval F P χ).comp hK.continuous_height)).bddBelow
  refine ⟨(1 : ℝ) ⊗ₜ[ℤ] χ, (m α : ℝ) * δ, -L - B,
    mul_pos (Nat.cast_pos.mpr hmα) hδ, fun z hz b hb ω hω R _ hLarge => ?_⟩
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hZc] at hz
  obtain ⟨a, _, hza⟩ := hz
  let aT := map F Z.toGrp T.toGrp (CommGroupScheme.groupHom zc) a
  let bT := map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) b.val
  have hzP : map F P G p (map F T.toGrp P tP aT) = z := by
    rw [← map_comp_apply_of_hom, htP]
    exact (map_comp_apply_of_hom (CommGroupScheme.groupHom zc) a).symm.trans hza
  have hbP : map F P G p (map F T.toGrp P tP bT) = positiveMap F G T i T₀ j b := by
    rw [← map_comp_apply_of_hom, htP]
    exact (map_comp_apply_of_hom (CommGroupScheme.groupHom j) b.val).symm
  have hzLog : characterLog F P (map F T.toGrp P tP aT) χ = 0 := by
    rw [htLog]
    apply Finset.sum_eq_zero
    intro β hβ
    have hzβ := root_restrict_eq_zero_of_isCentral i zc hZc.1.1.1 hZc.1.2 (hPositive β hβ).1
    have he : logNormHom F T aT β = 0 := by
      change characterLog F T.toGrp (map F Z.toGrp T.toGrp (CommGroupScheme.groupHom zc) a) β = 0
      rw [characterLog_map]
      change logNormHom F Z a (zc ≫ β) = 0
      rw [hzβ, map_zero]
    rw [he, mul_zero]
  have hbLog (β : characterLattice T) :
      logNormHom F T bT β = logNormHom F T₀ b.val (j ≫ β) := by
    change characterLog F T.toGrp (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) b.val) β = _
    rw [characterLog_map]
    rfl
  have hLo := (mem_weakSimpleRootChamber_iff_log F T₀ T j G i ν t b).mp hb
  have hValue (β : characterLattice T) (hβ : β ∈ s) :
      (n β : ℝ) * lt ≤ logNormHom F T bT β :=
    hn β _ lt (fun root hroot => by rw [hbLog]; exact hLo root hroot) hβ
  have hSumLower : L ≤ ∑ β ∈ s.erase α, (m β : ℝ) * logNormHom F T bT β := by
    dsimp only [L]
    apply Finset.sum_le_sum
    intro β hβ
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hValue β (Finset.mem_of_mem_erase hβ)) (Nat.cast_nonneg _)
  have hαLow : (m α : ℝ) * (δ * R) ≤ (m α : ℝ) * logNormHom F T bT α := by
    rw [hbLog]
    exact mul_le_mul_of_nonneg_left (hLarge α hα hαJ) (Nat.cast_nonneg _)
  have hωLow : B ≤ hK.height ω χ := hB ⟨ω, hω, rfl⟩
  rw [realParameterPairing_tmul, one_mul, ← hzP, ← hbP]
  simp only [mul_assoc]
  rw [hK.height_map_mul (map F T.toGrp P tP aT), hK.height_map_mul (map F T.toGrp P tP bT)]
  change _ ≤ characterLog F P (map F T.toGrp P tP aT) χ +
    (characterLog F P (map F T.toGrp P tP bT) χ + hK.height ω χ)
  rw [hzLog, zero_add, htLog, ← Finset.sum_erase_add _ _ hαs]
  linarith

end Langlands.Global
