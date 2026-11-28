import Langlands.Global.AdelicLeviFibrePairingExpansion
import Langlands.Global.AdelicFiniteLeviFibreProjection

/-! # Equality of the finite projection and original Levi pairings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "X₁" => NormOneRationalQuotient F M
local notation "dq₁" => normOneRationalQuotientHaarMeasure F M
local notation "jM" => fam.l J ≫ fam.p J
local notation "ι" => map F M G jM
local notation "Γ" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "Q₊" => PositiveRationalQuotient F M T i
local notation "V" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F M T i)
local notation "dq" => positiveRationalQuotientHaarMeasure F M T i
local notation "E" => positiveQuotientMeasurableEquiv F M T i hi I e hc
local notation "hM" => IsRationalLeviSubgroup.isConnectedReductive
  (ParabolicRootPresentationData.IsCompatible.levi (fam.isCompatible J))
local notation "S" => fullAEL2CuspidalSubmodule F M parabolicDynamic hM T i hi I e hc
local notation "δ" => fam.leviModulus J
local notation "d" => (fun b : Pos => Complex.ofReal ((δ (pp b) : ℝ)⁻¹))

omit [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant] in
private theorem integral_normOne_mul_conj_eq_inner {t : AM → ℂ}
    (htc : Continuous t) (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (u v : S) (hEq : (u.val : Q₊ → ℂ) =ᵐ[dq]
      positiveQuotientOfNormOneRestriction T i hi I e hc htc hti) :
    ∫ q : X₁, (v.val : Q₊ → ℂ) (E q) * starRingEnd ℂ (t ((Quotient.out q : A₁) : AM)) ∂dq₁ =
      inner ℂ u v := by
  let tQ := positiveQuotientOfNormOneRestriction T i hi I e hc htc hti
  have hval (q : X₁) : tQ (E q) = t ((Quotient.out q : A₁) : AM) := by
    let H := positiveQuotientHomeomorph F M T i hi I e hc
    change normOneRationalRestriction t (H.symm (H q)) = normOneRationalRestriction t q
    rw [Homeomorph.symm_apply_apply]
  have h := (measurePreserving_positiveQuotient F M T i hi I e hc).integral_comp'
    (fun z => (v.val : Q₊ → ℂ) z * starRingEnd ℂ (tQ z))
  simp only [hval] at h
  refine h.trans ?_
  change _ = inner ℂ u.val v.val
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hEq] with z hz
  rw [RCLike.inner_apply', hz, mul_comm]

private theorem leviPairing_leviFibreSmoothing_eq_fibreExpansion
    (hAvg : LeviRadicalAverageTestFunctionStatement.{u})
    (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    {N : ℕ} (rhoM : MatrixRepresentation M (Fin N)) (hN : 0 < N) (hrhoM : IsClosedSubgroup rhoM)
    (β : C_c(A, ℂ)) (hβ : IsAdelicTestFunction F G β) (f : AM → ℂ)
    (w : Pos → S) (hw : Continuous w)
    (t : AM → ℂ) (htc : Continuous t) (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (htCusp : HasZeroProperParabolicConstantTerms t) (htd : HasRapidDecayOnNormOneRepresentatives rhoM t)
    (hmatch : ∀ (b : Pos) (s : AM → ℂ) (hsc : Continuous s)
      (hsi : IsLeftInvariantUnder F M (rationalSubgroup F M) s)
      (_ : HasRapidDecayOnNormOneRepresentatives rhoM s) (v : S),
      (∀ (K : C_c(AM, ℂ)) (y : AM), normOnePartialConvolution T i K (v.val : Q₊ → ℂ) y =
        normOnePartialConvolution T i K (positiveQuotientOfNormOneRestriction T i hi I e hc hsc hsi) y) →
      inner ℂ v (w b) = ∫ q : X₁, let y := ((Quotient.out q : A₁) : AM)
        f (pp b * y) * starRingEnd ℂ (s y) ∂dq₁)
    (g : A) :
    fam.leviPairing J (fam.leviFibreSmoothing J T i hi I e hc β fun b => (w b).val) g t =
      ∫ b, fam.leviFibrePairingExpansionIntegrand J T i β f
        (positiveQuotientOfNormOneRestriction T i hi I e hc htc hti) g b ∂νP := by
  let hRed := (fam.isCompatible J).levi.isConnectedReductive
  let : IsAffineHom (fam.M J).X.hom := hRed.isAffineHom
  let t₁ := normOneRationalRestriction t
  let tQ := positiveQuotientOfNormOneRestriction T i hi I e hc htc hti
  have ht₁ : Measurable t₁ := (continuous_normOneRationalRestriction htc hti).measurable
  obtain ⟨C, _, hC⟩ := htd.exists_normOne_bound hti
  obtain ⟨vₜ, _, hvₜ⟩ := exists_cuspidalClass_of_bounded_normOneRestriction hM T i hi I e hc
    htc hti htCusp C hC
  rw [fam.leviPairing_leviFibreSmoothing_eq_integral J T i hi I e hc rhoM hN hrhoM β
    (fun b => (w b).val) (continuous_subtype_val.comp hw) t htc hti htd g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  let L := fam.leviFibrePairingKernel J T i β g b
  let s := normOnePartialConvolution T i L (vₜ.val : Q₊ → ℂ)
  obtain ⟨hsc, hsi, hsCusp⟩ := normOnePartialConvolution_cuspidalClass hM T i hi I e hc L vₜ
  have hsd := hasNormOneRepresentativeDecay_normOnePartialConvolution hM T i hi I e hc hDecay
    rhoM hN hrhoM L (fam.isAdelicTestFunction_leviFibrePairingKernel J T i hAvg β hβ g b) vₜ
  obtain ⟨D, _, hD⟩ := hsd.exists_normOne_bound hsi
  obtain ⟨vₛ, hvₛ, hconv⟩ := exists_cuspidalClass_of_bounded_normOneRestriction hM T i hi I e hc
    hsc hsi hsCusp D hD
  have hswap := fam.integral_leviFibreSmoothingIntegrand_mul_conj J T i hi I e hc β g b
    (w b).val t₁ ht₁ C (fun q => hC (Quotient.out q))
  change _ = (δ (pp b) : ℝ)⁻¹ • ∫ q : X₁, ((w b).val : Q₊ → ℂ) (E q) *
    starRingEnd ℂ (normOnePartialConvolution T i L tQ ((Quotient.out q : A₁) : AM)) ∂dq₁ at hswap
  refine hswap.trans ?_
  have hconv₀ (y : AM) : normOnePartialConvolution T i L tQ y = s y := (hvₜ L y).symm
  simp only [hconv₀]
  rw [fam.integral_normOne_mul_conj_eq_inner J T i hi I e hc hsc hsi vₛ (w b) hvₛ,
    hmatch b s hsc hsi hsd vₛ hconv]
  change _ = fam.leviFibrePairingExpansionIntegrand J T i β f tQ g b
  unfold leviFibrePairingExpansionIntegrand
  have hconv' (y : AM) :
      normOnePartialConvolution T i (fam.leviFibrePairingKernel J T i β g b) tQ y = s y :=
    hconv₀ y
  simp only [hconv']

/-- A finite expansion of the original Levi pairings yields the same pairings for the
finite smoothed projection. -/
theorem leviPairing_finiteLeviFibreProjection_eq_of_fibreExpansion
    (hAvg : LeviRadicalAverageTestFunctionStatement.{u})
    (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (K : Subgroup A) (hK : IsIwasawaCompact (fam.p J) K)
    {n : ℕ} (β : Fin n → C_c(A, ℂ)) (k : Fin n → A) (φ : A → ℂ) (c : ℝ)
    (hβ : ∀ j, IsAdelicTestFunction F G (β j)) (hφc : Continuous φ)
    (hφi : IsLeftInvariantUnder F G Γ φ) (hφh : HasHeightGrowth rho φ)
    (hExpansion : ∀ (s : AM → ℂ) (hsc : Continuous s)
      (hsi : IsLeftInvariantUnder F M (rationalSubgroup F M) s),
      HasRapidDecayOnNormOneRepresentatives (jM ≫ rho) s → ∀ g : A,
      fam.leviPairing J φ g s =
        c • ∑ j, ∫ b, fam.leviFibrePairingExpansionIntegrand J T i (β j) (fam.leviFibre J φ (k j))
          (positiveQuotientOfNormOneRestriction T i hi I e hc hsc hsi) g b ∂νP)
    (t : AM → ℂ) (htc : Continuous t) (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t)
    (htCusp : HasZeroProperParabolicConstantTerms t)
    (htd : HasRapidDecayOnNormOneRepresentatives (jM ≫ rho) t) (g : A) :
    fam.leviPairing J (fam.finiteLeviFibreProjection J T i hi I e hc β k φ c) g t =
      fam.leviPairing J φ g t := by
  let rhoM := jM ≫ rho
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : IsClosedImmersion (fam.l J).hom.hom.left := (fam.isCompatible J).levi.isClosedSubgroup
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  have hrhoM : IsClosedSubgroup rhoM := by
    change IsClosedImmersion ((fam.l J ≫ fam.p J) ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  have hL (j l : Fin n) : IsAdelicTestFunction F M (fam.radicalKernelCc J (β l) (k j) 1) :=
    fam.isAdelicTestFunction_radicalKernel J hAvg (hβ l) (k j) 1
  obtain ⟨hInt, r, hvec⟩ := fam.finiteLeviFibreVector_properties J T i hi I e hc β k φ c
    hDecay rho hN hrho hL hφc hφi hφh
  let W (j : Fin n) := fam.finiteLeviFibreVector J T i hi I e hc β k φ c j
  let f (j : Fin n) := fam.leviFibreSmoothing J T i hi I e hc (β j) fun b => (W j b).val
  let tQ := positiveQuotientOfNormOneRestriction T i hi I e hc htc hti
  have hφb (j : Fin n) :
      fam.leviPairing J (f j) g t = ∫ b, fam.leviFibrePairingExpansionIntegrand J T i
        (β j) (fam.leviFibre J φ (k j)) tQ g b ∂νP := by
    apply fam.leviPairing_leviFibreSmoothing_eq_fibreExpansion J T i hi I e hc hAvg hDecay
      rhoM hN hrhoM (β j) (hβ j) (fam.leviFibre J φ (k j)) (W j) (hvec j).1
      t htc hti htCusp htd _ g
    intro b s hsc hsi hsd v hconv
    let sQ := positiveQuotientOfNormOneRestriction T i hi I e hc hsc hsi
    let a₀ := ι (pp b) * k j
    have hrec : inner ℂ v (W j b) = fam.leviPairing J φ a₀ s := by
      rw [hExpansion s hsc hsi hsd a₀]
      change inner ℂ v (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b) = _
      rw [fam.inner_finiteLeviFibreVector J T i hi I e hc β k φ c j b v (fun l => hInt j l b)]
      refine congrArg (c • ·) (Finset.sum_congr rfl fun l _ => ?_)
      change _ = ∫ q, fam.leviFibrePairingExpansionIntegrand J T i (β l) (fam.leviFibre J φ (k l))
        sQ (ι (pp b) * k j) q ∂νP
      rw [fam.integral_leviFibrePairingExpansionIntegrand_mul_positive J T i hi I e hc]
      simp only [hconv, sQ]
    rw [hrec]
    unfold leviPairing leviPairingIntegrand leviFibre
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only [a₀]
    rw [← mul_assoc (ι _), ← map_mul, (positivePointMap_commute F M T i hc b _).eq]
  have hint (j : Fin n) : Integrable (fam.leviPairingIntegrand J (f j) g t) dq₁ := by
    obtain ⟨B, hB, hbound⟩ := (hvec j).2
    have hfc := fam.continuous_leviFibreSmoothing J T i hi I e hc (β j) _
      (continuous_subtype_val.comp (hvec j).1)
    have hfi := fam.isLeftInvariantUnder_leviFibreSmoothing J T i hi I e hc (β j)
      (fun b => (W j b).val)
    have hfh := fam.hasHeightGrowth_leviFibreSmoothing J T i hi I e hc rho hN hrho K hK (β j)
      (fun b => (W j b).val) B hB r hbound
    exact fam.integrable_leviPairingIntegrand_of_heightGrowth J rho hN hfh hfc hfi htc hti htd g
  have hsum : fam.leviPairing J (fam.finiteLeviFibreProjection J T i hi I e hc β k φ c) g t =
      c • ∑ j, fam.leviPairing J (f j) g t := by
    unfold leviPairing
    have hpoint (q : X₁) : fam.leviPairingIntegrand J
        (fam.finiteLeviFibreProjection J T i hi I e hc β k φ c) g t q =
        c • ∑ j, fam.leviPairingIntegrand J (f j) g t q := by
      simp only [leviPairingIntegrand, finiteLeviFibreProjection, f, W, Complex.real_smul,
        mul_assoc, Finset.sum_mul, smul_eq_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_smul,
      integral_finsetSum _ fun j _ => hint j]
  rw [hsum, hExpansion t htc hti htd g]
  exact congrArg (c • ·) (Finset.sum_congr rfl fun j _ => hφb j)

end Langlands.Global.StandardParabolicFamily
