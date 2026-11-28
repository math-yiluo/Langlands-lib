import Langlands.Global.AdelicLeviSiegelModulus
import Langlands.Global.AdelicSiegelLeviChamberShift
import Langlands.Global.AdelicNormOneSiegelIntegrability
import Langlands.Global.AdelicSiegelHalfModulus
import Langlands.Global.AdelicWeakConstantTermHalfModulusProof
import Langlands.Global.AdelicLocalFinitenessChamberCoordinates
import Langlands.Global.AdelicLeviCuspFormMajorantProof
import Langlands.Global.AdelicSquareIntegrableInducedNormOne
import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction

/-! # From ambient Siegel decay to the norm-one Levi integral -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal BigOperators Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus RepresentationGrowth
  InducedInnerProductIntegrable Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))
  (J : StandardIndex F G fam.i fam.ν)

local notation "M" => fam.M J
local notation "lG" => fam.l J ≫ fam.p J
local notation "A" => AdelicGroupPoints F G
local notation "A_M" => AdelicGroupPoints F M
local notation "mG" => map F M G lG
local notation "Torus" => intrinsicSubgroup F T₀
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "δ" => siegelModulus F G fam.T fam.i fam.ν T₀ j
local notation "σ" => (fun a : Torus => 1 + Real.log (adelicHeight F G rho (aG a)))
local notation "chamber" => weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν
local notation "rootLog" => (fun (a : Torus) (β : characterLattice fam.T) =>
  characterLog F T₀.toGrp a.val (j ≫ β))

/-- Rapid logarithmic decay on the ambient chamber with the complementary
simple-root logarithms bounded above. -/
def HasSiegelLogDecayAlongLevi (w : A → ℂ) : Prop :=
  ∀ (t : ℝ≥0ˣ) (Ω : Set A), IsCompact Ω → ∀ B : ℝ, 0 ≤ B → ∀ p : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ chamber t, (∀ β ∈ Δ \ J.val, rootLog a β ≤ B) →
      ∀ x ∈ Ω, ‖w (aG a * x)‖ * (σ a) ^ p ≤ C * Real.sqrt (δ a)

private theorem exists_rootLog_abs_le_ambientHeight (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (β : characterLattice fam.T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Torus, |rootLog a β| ≤ C * σ a := by
  obtain ⟨C, hC, e, hBound⟩ := exists_characterNorm_le F (fam.i ≫ rho) hN
    (IsClosedSubgroup.comp fam.maximalSplit.isSplitSubtorus.2 hrho) β
  refine ⟨Real.log C + e, add_nonneg (Real.log_nonneg hC) (Nat.cast_nonneg _), ?_⟩
  intro a
  let z := map F T₀.toGrp fam.T.toGrp (CommGroupScheme.groupHom j) a.val
  let r : ℝ := ((characterNorm F fam.T.toGrp β.toMul z : ℝ≥0) : ℝ)
  have hr : 0 < r := by
    exact_mod_cast (characterNorm F fam.T.toGrp β.toMul z).ne_zero.bot_lt
  have hLog : rootLog a β = Real.log r := by
    change Real.log ((characterNorm F T₀.toGrp (CommGroupScheme.groupHom j ≫ β.toMul)
      a.val : ℝ≥0) : ℝ) = _
    rw [characterNorm_comp]
  have hHeight : adelicHeight F fam.T.toGrp (fam.i ≫ rho) z = adelicHeight F G rho (aG a) := by
    rw [← adelicHeight_map_eq_adelicHeight_comp, ← map_comp_apply_of_hom]
    rfl
  have hb₁ : r ≤ C * adelicHeight F G rho (aG a) ^ e := by
    simpa only [hHeight] using (hBound z).1
  have hb₂ : r⁻¹ ≤ C * adelicHeight F G rho (aG a) ^ e := by
    simpa only [Units.val_inv_eq_inv_val, NNReal.coe_inv, hHeight] using (hBound z).2
  have hH := one_le_adelicHeight F G rho hN (aG a)
  have hσ : 1 ≤ σ a := le_add_of_nonneg_right (Real.log_nonneg hH)
  rw [hLog]
  refine (abs_log_le_of_le_of_inv_le hr hC hH e hb₁ hb₂).trans ?_
  calc
    _ ≤ Real.log C * σ a + (e : ℝ) * σ a :=
      add_le_add (le_mul_of_one_le_right (Real.log_nonneg hC) hσ)
        (mul_le_mul_of_nonneg_left (by dsimp only; linarith) (Nat.cast_nonneg _))
    _ = _ := (add_mul _ _ _).symm

omit [NumberField F] in
private theorem levi_torus_structure :
    letI := (fam.isCompatible J).levi.isConnectedReductive.isAffineHom
    IsMaximalSplitTorus (fam.torus J) ∧ IsGenericCocharacter (fam.torus J) fam.ν ∧
      simpleRelativeRoots (fam.torus J) fam.ν = J.val := by
  let hM := (fam.isCompatible J).levi.isConnectedReductive
  let hClosed := (fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup
  let : IsAffineHom (fam.M J).X.hom := hM.isAffineHom
  let : Mono (lG : M ⟶ G).hom.hom.left := hClosed.mono
  let : Mono (lG : M ⟶ G).hom.hom := Over.mono_of_mono_left _
  have hRep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy lG :=
    ⟨inferInstance, (fam.isCompatible J).levi_eq⟩
  have hTorus : standardLeviTorusFactor fam.i fam.ν J.val hRep = fam.torus J := by
    apply Grp.hom_ext
    apply (cancel_mono (lG : M ⟶ G).hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, standardLeviTorusFactor_comp,
      fam.torus_comp J]
  have hMax := fam.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor
    fam.i fam.ν J.val hRep hClosed
  obtain ⟨hRoots, hν, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
    F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic
    J.val J.property M hM lG hRep hClosed
  rw [hTorus] at hMax hRoots hν
  exact ⟨hMax, hν, hRoots⟩

section LeviChamber

variable [IsAffineHom (fam.M J).X.hom]
  {T₁ : CommGroupScheme (Spec (CommRingCat.of F))} (k : T₁ ⟶ fam.T)

local notation "TorusM" => intrinsicSubgroup F T₁
local notation "bM" => positiveMap F M fam.T (fam.torus J) T₁ k
local notation "δM" => siegelModulus F M fam.T (fam.torus J) fam.ν T₁ k
local notation "σM" => siegelRootLogSize (fam.torus J) fam.ν k
local notation "chamberM" => weakSimpleRootChamber F T₁ fam.T k M (fam.torus J) fam.ν
local notation "rootLogM" => (fun (b : TorusM) (β : characterLattice fam.T) =>
  characterLog F T₁.toGrp (Subtype.val b) (k ≫ β))

/-- The ambient estimate restricts to the positive Levi chamber, with the Levi
root logarithmic size and the Levi modulus. -/
theorem exists_leviChamberLogDecay
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (hsetupM : IsSiegelAlgebraicSetup F M fam.T (fam.torus J) fam.ν T₁ k)
    (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {w : A → ℂ} (hDecay : fam.HasSiegelLogDecayAlongLevi j rho J w)
    {lam : ComplexCharacterParameter F (fam.P J)} (hunit : parameterRealPart F (fam.P J) lam = 0)
    (hEig : ∀ b : fam.positiveSplitComponent J, fam.splitComponentRepresentation J b w =
      parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) b.val • w)
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ chamberM t, ∀ x ∈ Ω,
      ‖w (mG (bM b) * x)‖ * (σM b) ^ p ≤ C * Real.sqrt (δM b) := by
  classical
  have hClosed := (fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup
  let : Mono (lG : M ⟶ G).hom.hom.left := hClosed.mono
  have hRep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy lG :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible J).levi_eq⟩
  have hRoots := (fam.levi_torus_structure J).2.2
  have hFin := fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν
  let : Fintype J.val := (hFin.subset J.property).fintype
  choose Cα hCα hBound using fun α : J.val => fam.exists_rootLog_abs_le_ambientHeight j rho hN hrho α.val
  let V := 1 + ∑ α : J.val, Cα α
  have hV : 0 ≤ V := add_nonneg zero_le_one (Finset.sum_nonneg fun α _ => hCα α)
  obtain ⟨B, hB, hShift⟩ := fam.exists_siegelLeviChamberShift j hsetup J
  let t' := min t 1
  have hLogLow : Real.log ((t' : ℝ≥0) : ℝ) ≤ Real.log ((t : ℝ≥0) : ℝ) :=
    (log_unit_le_log_unit_iff t' t).mpr (min_le_left _ _)
  have hLogZero : Real.log ((t' : ℝ≥0) : ℝ) ≤ 0 := by
    simpa only [Units.val_one, NNReal.coe_one, Real.log_one] using
      (log_unit_le_log_unit_iff t' 1).mpr (min_le_right _ _)
  obtain ⟨C, hC, hMain⟩ := hDecay t' Ω hΩ B hB p
  refine ⟨C * V ^ p, mul_nonneg hC (pow_nonneg hV _), ?_⟩
  intro b hb x hx
  let bT : intrinsicSubgroup F fam.T :=
    ⟨map F T₁.toGrp fam.T.toGrp (CommGroupScheme.groupHom k) b.val,
      map_intrinsicSubgroup_le F T₁ fam.T k ⟨b.val, b.property, rfl⟩⟩
  have hbVal : mG (bM b) = map F fam.T.toGrp G fam.i bT.val := by
    change mG (map F T₁.toGrp M (CommGroupScheme.groupHom k ≫ fam.torus J) b.val) = _
    rw [← map_comp_apply_of_hom, Category.assoc, fam.torus_comp J, map_comp_apply_of_hom]
  have hb₁ := hsetupM.positiveMap_mem_normOne F M fam.T (fam.torus J) fam.ν T₁ k b
  have hbLog : characterLog F G (map F fam.T.toGrp G fam.i bT.val) = 0 :=
    (characterLog_eq_zero_iff F G _).mpr
      (hbVal ▸ map_normOneSubgroup_le F M G lG ⟨bM b, hb₁, rfl⟩)
  obtain ⟨a, hab⟩ := fam.exists_siegelTorus_lift_of_characterLog_eq_zero j hsetup bT hbLog
  have hValue : aG a = mG (bM b) := by
    rw [hbVal]
    change map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ fam.i) a.val = _
    rw [map_comp_apply_of_hom, hab]
  have hLogs (β : characterLattice fam.T) : rootLog a β = rootLogM b β := by
    have h := congrArg (fun z => characterLog F fam.T.toGrp z β) hab
    change characterLog F fam.T.toGrp
      (map F T₀.toGrp fam.T.toGrp (CommGroupScheme.groupHom j) a.val) β =
        characterLog F fam.T.toGrp
          (map F T₁.toGrp fam.T.toGrp (CommGroupScheme.groupHom k) b.val) β at h
    rw [characterLog_map, characterLog_map] at h
    exact h
  obtain ⟨s, u, hu, hKeep, hCompl⟩ := hShift a
  let v := s * a
  have hv : v ∈ chamber t' := by
    apply (mem_weakSimpleRootChamber_iff_log F T₀ fam.T j G fam.i fam.ν t' v).mpr
    intro β hβ
    by_cases hJ : β ∈ J.val
    · have hbβ : β ∈ simpleRelativeRoots (fam.torus J) fam.ν := hRoots.symm ▸ hJ
      have h := (mem_weakSimpleRootChamber_iff_log F T₁ fam.T k M (fam.torus J)
        fam.ν t b).mp hb β hbβ
      change Real.log ((t' : ℝ≥0) : ℝ) ≤ rootLog (s * a) β
      rw [hKeep β hJ, hLogs]
      exact hLogLow.trans h
    · exact hLogZero.trans (hCompl β hβ hJ).1
  have hSize : σM b ≤ V * σ v := by
    have hσ : 1 ≤ σ v := le_add_of_nonneg_right
      (Real.log_nonneg (one_le_adelicHeight F G rho hN (aG v)))
    rw [siegelRootLogSize, hRoots, finsum_eq_sum_of_fintype]
    dsimp only [V]
    rw [add_mul, Finset.sum_mul, one_mul]
    refine add_le_add hσ (Finset.sum_le_sum fun α _ => ?_)
    change |rootLogM b α.val| ≤ Cα α * σ v
    rw [← hLogs, ← hKeep α.val α.property]
    exact hBound α v
  have hδ := siegelModulus_eq_levi_of_normOne fam.i fam.ν fam.connectedReductive fam.maximalSplit
    fam.generic J.val J.property hRep (fam.torus J) (fam.torus_comp J) j k a b hab hb₁
  have hAbs : ‖parameterPower F (fam.P J) lam u.val‖ = 1 := by
    rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, hunit, map_zero,
      LinearMap.zero_apply, Real.exp_zero]
  have hEigenNorm :
      ‖parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) u.val‖ =
        Real.sqrt (δ s) := by
    rw [parameterPower_add, norm_mul, hAbs, one_mul]
    change ‖fam.halfModulus J u.val‖ = _
    rw [fam.halfModulus_eq_siegelSqrt_of_positiveSplitComponent standardNestedHalfModulusCompatibility
      hsetup J s u hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsPos : 0 < Real.sqrt (δ s) := by
    rw [← hEigenNorm]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hSeval : ‖w (aG v * x)‖ = Real.sqrt (δ s) * ‖w (aG a * x)‖ := by
    have h := congrFun (hEig u) (aG a * x)
    change w (map F (fam.P J) G (fam.p J) u.val * (aG a * x)) =
      parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) u.val * w (aG a * x) at h
    change ‖w (aG (s * a) * x)‖ = _
    rw [map_mul, mul_assoc, ← hu, h, norm_mul, hEigenNorm]
  have hPositiveRoots := (fam.maximalSplit.isSplitSubtorus.1.finite_relativeRoots fam.i).subset
    (positiveRelativeRoots_subset_relativeRoots fam.i fam.ν)
  have hModMul : δ v = δ s * δ a := by
    simp only [v, siegelModulus, finprod_mem_eq_finite_toFinset_prod _ hPositiveRoots,
      Subgroup.coe_mul, map_mul, Units.val_mul, NNReal.coe_mul, mul_pow, Finset.prod_mul_distrib]
  have h := hMain v hv (fun β hβ => (hCompl β hβ.1 hβ.2).2) x hx
  rw [hSeval, hModMul, Real.sqrt_mul (Real.sqrt_pos.mp hsPos).le, hδ] at h
  have hCancel : ‖w (aG a * x)‖ * (σ v) ^ p ≤ C * Real.sqrt (δM b) := by
    apply le_of_mul_le_mul_left _ hsPos
    calc
      _ = (Real.sqrt (δ s) * ‖w (aG a * x)‖) * (σ v) ^ p := (mul_assoc _ _ _).symm
      _ ≤ C * (Real.sqrt (δ s) * Real.sqrt (δM b)) := h
      _ = _ := mul_left_comm _ _ _
  calc ‖w (mG (bM b) * x)‖ * (σM b) ^ p ≤ ‖w (aG a * x)‖ * (V * σ v) ^ p := by
          rw [hValue]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (zero_le_one.trans (one_le_siegelRootLogSize (fam.torus J) fam.ν k b)) hSize _) (norm_nonneg _)
    _ ≤ C * V ^ p * Real.sqrt (δM b) := by
          rw [mul_pow]
          calc
            _ = V ^ p * (‖w (aG a * x)‖ * (σ v) ^ p) := mul_left_comm _ _ _
            _ ≤ V ^ p * (C * Real.sqrt (δM b)) := mul_le_mul_of_nonneg_left hCancel (pow_nonneg hV _)
            _ = _ := by rw [← mul_assoc, mul_comm (V ^ p) C]

end LeviChamber

private theorem square_le_of_logDecay {f C delta s : ℝ} {p : ℕ}
    (hf : 0 ≤ f) (hC : 0 ≤ C) (hδ : 0 ≤ delta) (hs : 1 ≤ s)
    (h : f * s ^ p ≤ C * Real.sqrt delta) :
    f ^ 2 ≤ C ^ 2 * delta * s⁻¹ ^ p := by
  have hpos : 0 < s := one_pos.trans_le hs
  have hnorm := (le_div_iff₀ (pow_pos hpos p)).mpr h
  rw [div_eq_mul_inv, ← inv_pow] at hnorm
  calc
    _ ≤ (C * Real.sqrt delta * s⁻¹ ^ p) ^ 2 := pow_le_pow_left₀ hf hnorm 2
    _ = C ^ 2 * delta * (s⁻¹ ^ p) ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hδ]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by
        rw [pow_two]
        exact mul_le_of_le_one_right (pow_nonneg (inv_nonneg.mpr hpos.le) _)
          (pow_le_one₀ (inv_nonneg.mpr hpos.le) (inv_le_one₀ hpos |>.mpr hs)))
      (mul_nonneg (pow_nonneg hC _) hδ)

/-- A continuous parabolic-invariant eigenvector satisfying the ambient logarithmic
decay has integrable absolute square on the norm-one Levi slice and the compact. -/
theorem integrable_normOneLeviSquare_of_siegelLogDecay
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    {K : Subgroup A} (hK : IsCompact (K : Set A)) {w : A → ℂ} (hc : Continuous w)
    (hInv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)) w)
    (hDecay : fam.HasSiegelLogDecayAlongLevi j rho J w)
    {lam : ComplexCharacterParameter F (fam.P J)} (hunit : parameterRealPart F (fam.P J) lam = 0)
    (hEig : ∀ b : fam.positiveSplitComponent J, fam.splitComponentRepresentation J b w =
      parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) b.val • w) :
    Integrable (fam.normOneLeviSquare J w : K × NormOneRationalQuotient F M → ℝ)
      ((compactHaarProbability F G K hK).prod (normOneRationalQuotientHaarMeasure F M)) := by
  let hM := (fam.isCompatible J).levi.isConnectedReductive
  let : IsAffineHom (fam.M J).X.hom := hM.isAffineHom
  have hClosed := (fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup
  obtain ⟨hMax, hGeneric, _⟩ := fam.levi_torus_structure J
  obtain ⟨T₁, k, hsetupM⟩ := exists_siegelAlgebraicSetup_of_generic F (fam.torus J) fam.ν hM hMax hGeneric
  let bM := positiveMap F M fam.T (fam.torus J) T₁ k
  let δM := siegelModulus F M fam.T (fam.torus J) fam.ν T₁ k
  let σM := siegelRootLogSize (fam.torus J) fam.ν k
  let chamberM := weakSimpleRootChamber F T₁ fam.T k M (fam.torus J) fam.ν
  obtain ⟨C, t, W, d, L, hW, _, hL, hBound⟩ :=
    exists_normOneSiegelIntegralBound (fam.torus J) fam.ν k hM hsetupM
  obtain ⟨S, hS, hSmem⟩ := exists_isCompact_conj_unipotent hM hsetupM (lG ≫ rho)
    (IsClosedSubgroup.comp hClosed hrho) C.omegaN C.compact_omegaN t
  let iN := map F _ M (Standard.unipotentHom (fam.torus J) fam.ν ∅)
  let iM := map F _ M (Standard.leviHom (fam.torus J) fam.ν ∅)
  let m₁ (m : normOneSubgroup F (Standard.leviScheme (fam.torus J) fam.ν ∅)) : A_M := iM m.val
  let ΩM : Set A_M := S * (m₁ '' C.omegaM) * (C.compactSubgroup : Set A_M) * W
  have hΩM : IsCompact ΩM :=
    ((hS.mul (C.compact_omegaM.image (iM.continuous.comp continuous_subtype_val))).mul
      C.compact_compactSubgroup).mul hW.isCompact
  let Ω : Set A := (mG '' ΩM) * (K : Set A)
  have hΩ : IsCompact Ω := (hΩM.image (map F M G lG).continuous).mul hK
  obtain ⟨B, hB, hDecayM⟩ :=
    fam.exists_leviChamberLogDecay j rho J k hsetup hsetupM hN hrho hDecay hunit hEig t Ω hΩ d
  let f (x : K) (m : A_M) : ℝ :=
    ‖w (map F (fam.P J) G (fam.p J) (map F M (fam.P J) (fam.l J) m) * x.val)‖ ^ 2
  have hf (x : K) : Continuous (f x) := by
    apply Continuous.pow _ 2
    exact (hc.comp (((map F (fam.P J) G (fam.p J)).continuous.comp
      (map F M (fam.P J) (fam.l J)).continuous).mul continuous_const)).norm
  have hfInv (x : K) (q : A_M) (hq : q ∈ rationalSubgroup F M) (m : A_M) :
      f x (q * m) = f x m := by
    dsimp only [f]
    rw [form_rational_mul hInv hq m x.val]
  have hChart (x : K) :
      ∀ b ∈ chamberM t, ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ u ∈ C.compactSubgroup, ∀ v ∈ W,
        ENNReal.ofReal (f x (iN n * m₁ m * bM b * u * v)) ≤
          ENNReal.ofReal (B ^ 2) * (siegelModulusNN (i := fam.torus J) (ν := fam.ν) (j := k) b : ℝ≥0∞) *
            ENNReal.ofReal ((σM b)⁻¹ ^ d) := by
    intro b hb n hn m hm u hu v hv
    have hcomm : Commute (bM b) (m₁ m) := by
      change Commute (map F T₁.toGrp M (CommGroupScheme.groupHom k ≫ fam.torus J) b.val) (m₁ m)
      rw [map_comp_apply_of_hom]
      exact hsetupM.commute_torus_minimalLevi F M fam.T (fam.torus J) fam.ν T₁ k
        (map F T₁.toGrp fam.T.toGrp (CommGroupScheme.groupHom k) b.val) m.val
    let y := (bM b)⁻¹ * iN n * bM b * m₁ m * u * v
    have hy : y ∈ ΩM :=
      Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (hSmem n hn b hb) ⟨m, hm, rfl⟩) hu) hv
    have hprod : iN n * m₁ m * bM b * u * v = bM b * y := by
      calc iN n * m₁ m * bM b * u * v = iN n * (m₁ m * bM b) * u * v := by rw [mul_assoc (iN n)]
        _ = iN n * (bM b * m₁ m) * u * v := by rw [← hcomm.eq]
        _ = bM b * y := by simp only [y, mul_assoc, mul_inv_cancel_left]
    have hxy : mG y * x.val ∈ Ω := Set.mul_mem_mul ⟨y, hy, rfl⟩ x.property
    have hAt := hDecayM b hb (mG y * x.val) hxy
    have hValue : f x (iN n * m₁ m * bM b * u * v) = ‖w (mG (bM b) * (mG y * x.val))‖ ^ 2 := by
      dsimp only [f]
      rw [hprod, ← map_comp_apply_of_hom, map_mul, mul_assoc]
    have hδEq : ((siegelModulusNN (i := fam.torus J) (ν := fam.ν) (j := k) b : ℝ≥0) : ℝ) =
        δM b := coe_siegelModulusNN _
    have hδ₀ : 0 ≤ δM b := hδEq ▸ NNReal.coe_nonneg _
    rw [hValue]
    calc
      _ ≤ ENNReal.ofReal ((B ^ 2 * δM b) * (σM b)⁻¹ ^ d) :=
        ENNReal.ofReal_le_ofReal (square_le_of_logDecay (norm_nonneg _) hB hδ₀
          (one_le_siegelRootLogSize (fam.torus J) fam.ν k b) hAt)
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg B) hδ₀), ENNReal.ofReal_mul (sq_nonneg B),
          ← hδEq, ENNReal.ofReal_coe_nnreal]
  let mu := normOneRationalQuotientHaarMeasure F M
  let κ := compactHaarProbability F G K hK
  let : IsFiniteMeasure mu :=
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M hM
  let : IsProbabilityMeasure κ := compactHaarProbability_isProbabilityMeasure F G K hK
  have hF (x : K) :
      ∫⁻ q : NormOneRationalQuotient F M, ENNReal.ofReal (f x q.out.val) ∂mu ≤ ENNReal.ofReal (B ^ 2) * L :=
    hBound (fun m => ENNReal.ofReal (f x m)) (hf x).measurable.ennreal_ofReal
      (fun q hq m => congrArg ENNReal.ofReal (hfInv x q hq m)) _ (hChart x)
  have hJoint : Continuous (fun z : K × normOneSubgroup F M => f z.1 z.2.val) :=
    (hc.comp (((map F (fam.P J) G (fam.p J)).continuous.comp ((map F M (fam.P J) (fam.l J)).continuous.comp
      (continuous_subtype_val.comp continuous_snd))).mul (continuous_subtype_val.comp continuous_fst))).norm.pow 2
  have hCont : Continuous (fam.normOneLeviSquare J w : K × NormOneRationalQuotient F M → ℝ) := by
    apply LeftCosetSpace.continuous_out_of_invariant (rationalNormOneSubgroup F M) (fun x m => f x m.val) hJoint
    intro x q hq m
    exact hfInv x q.val (rationalNormOneSubgroupInclusion F M ⟨q, hq⟩).property m.val
  refine ⟨hCont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mpr ?_⟩
  have hMeas : Measurable (fun z : K × NormOneRationalQuotient F M => ENNReal.ofReal (f z.1 z.2.out.val)) :=
    hCont.measurable.ennreal_ofReal
  change (∫⁻ z : K × NormOneRationalQuotient F M, ENNReal.ofReal (f z.1 z.2.out.val) ∂(κ.prod mu)) < ∞
  rw [lintegral_prod _ hMeas.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : K, ENNReal.ofReal (B ^ 2) * L ∂κ := lintegral_mono hF
    _ < ∞ := by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors Automorphic.GroupSchemeFunctions

/-- The ambient chamber decay of an ordinary eigenvector with unitary normalized
parameter implies square integrability on the norm-one Levi and a compact subgroup. -/
def AdelicLeviSiegelDecayStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)),
    IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j → 0 < N → IsClosedSubgroup rho →
    ∀ (J : StandardIndex F G fam.i fam.ν) (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsCompact (K : Set (AdelicGroupPoints F G))) (w : AdelicGroupPoints F G → ℂ),
    Continuous w →
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)) w →
    fam.HasSiegelLogDecayAlongLevi j rho J w →
    ∀ lam : ComplexCharacterParameter F (fam.P J), parameterRealPart F (fam.P J) lam = 0 →
    (∀ b : fam.positiveSplitComponent J, fam.splitComponentRepresentation J b w =
      parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) b.val • w) →
    Integrable (fam.normOneLeviSquare J w : K × NormOneRationalQuotient F (fam.M J) → ℝ)
      ((compactHaarProbability F G K hK).prod (normOneRationalQuotientHaarMeasure F (fam.M J)))

theorem adelicLeviSiegelDecay : AdelicLeviSiegelDecayStatement := by
  intro F _ _ G _ _ _ fam T₀ j N rho hsetup hN hrho J K hK w hc hInv hDecay lam hunit hEig
  exact fam.integrable_normOneLeviSquare_of_siegelLogDecay j rho J hsetup hN hrho hK hc hInv hDecay hunit hEig

end Langlands.Global
