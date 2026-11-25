import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralKernelStep
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationPairing
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # The diagonal of the VIII.4.1 kernel as conjugation pairings

The diagonal `α_χ(x, x)` of Waldspurger's kernel is a finite combination of the bilinear
conjugation pairings `(E, 1_{H a})(x⁻¹)` of `RationalConjugationPairing` when `E` vanishes
outside a normal subgroup `N ⊇ H` whose intersection with `A` is compact, and `χ` is trivial on
`A ∩ H`.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate ENNReal

namespace Langlands.HarishChandraSchwartz

universe u uG

section Diagonal

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μG : Measure G} {H : Subgroup G}

/-- The characteristic function `g ↦ 1_H(g a⁻¹)` of the right coset `H a`. -/
def rightCosetIndicator (H : Subgroup G) (a : G) (g : G) : ℂ :=
  (H : Set G).indicator (fun _ => (1 : ℂ)) (g * a⁻¹)

omit [IsTopologicalGroup G] in
/-- `∫_H E(x⁻¹ h a x) dh = ∫_G E(x⁻¹ g x) 1_{H a}(g) dg`, the conjugation pairing of `E` and
`1_{H a}` at `x⁻¹`, for the restriction of a right-invariant `μ_G` to the open subgroup `H`. -/
theorem integral_comap_eq_conjugationPairing (hHo : IsOpen (H : Set G)) [MeasurableMul G]
    [μG.IsMulRightInvariant] (E : G → ℂ) (a x : G) :
    ∫ h, E (x⁻¹ * h * (a * x)) ∂(μG.comap H.subtype) =
      conjugationPairing μG E (rightCosetIndicator H a) x⁻¹ := by
  have h1 : ∫ h, E (x⁻¹ * h * (a * x)) ∂(μG.comap H.subtype) =
      ∫ g in (H : Set G), E (x⁻¹ * g * (a * x)) ∂μG :=
    integral_subtype_comap hHo.measurableSet (fun g => E (x⁻¹ * g * (a * x)))
  rw [h1, ← integral_indicator hHo.measurableSet,
    ← integral_mul_right_eq_self _ a⁻¹]
  unfold conjugationPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [conjugationIntegrand, rightCosetIndicator]
  by_cases hg : g * a⁻¹ ∈ (H : Set G)
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, mul_one]
    congr 1
    group
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]

omit [IsTopologicalGroup G] in
/-- The diagonal of the kernel: `α_χ(x, x) = mes(H)⁻² ∫_A χ(a) (E, 1_{H a})(x⁻¹) da`. -/
theorem kernelAlphaChi_self_eq (hHo : IsOpen (H : Set G)) [MeasurableMul G]
    [μG.IsMulRightInvariant] {A : Subgroup G} [MeasurableSpace A] [MeasurableInv A]
    {μA : Measure A} [μA.IsInvInvariant] (hAc : A ≤ Subgroup.center G) (χ : A →* ℂˣ)
    (E : G → ℂ) (x : G) :
    kernelAlphaChi μA χ (μG.comap H.subtype) E x x =
      (((μG.comap H.subtype Set.univ).toReal : ℂ)⁻¹) ^ 2 *
        ∫ a, (χ a : ℂ) * conjugationPairing μG E (rightCosetIndicator H a) x⁻¹ ∂μA := by
  rw [kernelAlphaChi_eq hAc, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [kernelAlpha]
  rw [integral_comap_eq_conjugationPairing hHo]
  ring

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- If `E` vanishes outside a normal subgroup `N ⊇ H` and `a ∉ N`, the pairing with `1_{H a}`
vanishes. -/
theorem conjugationPairing_rightCosetIndicator_eq_zero {N : Subgroup G} [N.Normal]
    (hHN : H ≤ N) {E : G → ℂ} (hE : ∀ y, y ∉ N → E y = 0) {a : G} (ha : a ∉ N) (x : G) :
    conjugationPairing μG E (rightCosetIndicator H a) x = 0 := by
  unfold conjugationPairing
  have h0 : ∀ g, conjugationIntegrand E (rightCosetIndicator H a) x g = 0 := by
    intro g
    simp only [conjugationIntegrand, rightCosetIndicator]
    by_cases hg : g * a⁻¹ ∈ (H : Set G)
    · have hgN : g ∉ N := fun hgN => ha (by
        have h2 := N.mul_mem (N.inv_mem hgN) (hHN hg)
        have h3 : a⁻¹ ∈ N := by simpa using h2
        simpa using N.inv_mem h3)
      have hxN : x * g * x⁻¹ ∉ N := fun h => hgN (by
        simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem _ h x⁻¹)
      rw [hE _ hxN, zero_mul]
    · rw [Set.indicator_of_notMem hg, mul_zero]
  simp [h0]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- `1_{H a b} = 1_{H a}` for central `a` and `b ∈ H`. -/
theorem rightCosetIndicator_mul_of_mem {a b : G} (ha : a ∈ Subgroup.center G) (hb : b ∈ H) :
    rightCosetIndicator H (a * b) = rightCosetIndicator H a := by
  funext g
  have hc : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ ha) b⁻¹
  have e : g * (a * b)⁻¹ = g * a⁻¹ * b⁻¹ := by
    rw [mul_inv_rev, hc, mul_assoc]
  simp only [rightCosetIndicator, e]
  by_cases hg : g * a⁻¹ ∈ (H : Set G)
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem]
    exact H.mul_mem hg (H.inv_mem hb)
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem]
    exact fun h => hg (by simpa using H.mul_mem h hb)

/-- **Integrability of the diagonal of the VIII.4.1 kernel.** Let `A` be central, `χ` trivial on
`A ∩ H`, and let `E` vanish outside an open normal subgroup `N ⊇ H` with `{a ∈ A | a ∈ N}`
compact. If every pairing `q ↦ (E, 1_{H a})(q̇⁻¹)` is integrable on `A \ G`, then so is
`q ↦ Re α_χ(q̇, q̇)`. Indeed `α_χ(x, x)` is a finite combination of these pairings: the
integrand over `A` vanishes outside the compact set `A ∩ N` and is constant on cosets of
`A ∩ H`. -/
theorem integrable_kernelAlphaChi_self (hHo : IsOpen (H : Set G)) [MeasurableMul G]
    [μG.IsMulRightInvariant] {A : Subgroup G} [MeasurableSpace A] [BorelSpace A]
    [MeasurableInv A] {μA : Measure A} [μA.IsInvInvariant] [IsFiniteMeasureOnCompacts μA]
    (hAc : A ≤ Subgroup.center G) {χ : A →* ℂˣ} (hχH : ∀ b : A, (b : G) ∈ H → χ b = 1)
    {N : Subgroup G} [N.Normal] (hNo : IsOpen (N : Set G)) (hHN : H ≤ N)
    (hAN : IsCompact {a : A | (a : G) ∈ N}) {E : G → ℂ} (hE : ∀ y, y ∉ N → E y = 0)
    [MeasurableSpace (LeftQuotient A)] {ν : Measure (LeftQuotient A)}
    (hP : ∀ a : A, Integrable (fun q : LeftQuotient A =>
      conjugationPairing μG E (rightCosetIndicator H a) (q.out)⁻¹) ν) :
    Integrable (fun q : LeftQuotient A =>
      (kernelAlphaChi μA χ (μG.comap H.subtype) E q.out q.out).re) ν := by
  classical
  set S : Set A := {a : A | (a : G) ∈ N} with hSdef
  have hSo : IsOpen S := hNo.preimage continuous_subtype_val
  have hSm : MeasurableSet S := hSo.measurableSet
  have : CompactSpace S := isCompact_iff_compactSpace.mp hAN
  set μS : Measure S := μA.comap Subtype.val with hμS
  have : IsFiniteMeasure μS := ⟨by
    rw [hμS, (MeasurableEmbedding.subtype_coe hSm).comap_apply, Set.image_univ,
      Subtype.range_coe]
    exact hAN.measure_lt_top⟩
  set P : A → G → ℂ := fun a x =>
    (χ a : ℂ) * conjugationPairing μG E (rightCosetIndicator H a) x⁻¹ with hPdef
  set F : S → G → ℂ := fun s => P s with hFdef
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have hopen : IsOpen {s' : S | ((s : A) : G)⁻¹ * ((s' : A) : G) ∈ H} :=
      hHo.preimage (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val))
    filter_upwards [hopen.mem_nhds (by simp [H.one_mem])] with s' hs'
    set b : A := (s : A)⁻¹ * s' with hb
    have hbH : (b : G) ∈ H := by simpa [hb] using hs'
    have hs'eq : (s' : A) = (s : A) * b := by simp [hb]
    funext x
    simp only [hFdef, hPdef, hs'eq, map_mul, hχH b hbH, mul_one, Subgroup.coe_mul]
    rw [rightCosetIndicator_mul_of_mem (hAc (s : A).2) hbH]
  have hsum : ∀ x, ∫ a, P a x ∂μA =
      ∑ c ∈ hFlc.range_finite.toFinset, (μS.real (F ⁻¹' {c}) : ℂ) * c x := by
    intro x
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun a ha => ?_)]
    · rw [← integral_subtype_comap hSm (fun a => P a x)]
      exact integral_apply_eq_sum_of_isLocallyConstant hFlc x
    · simp only [hPdef]
      rw [conjugationPairing_rightCosetIndicator_eq_zero hHN hE ha, mul_zero]
  have hdiag : ∀ x, kernelAlphaChi μA χ (μG.comap H.subtype) E x x =
      (((μG.comap H.subtype Set.univ).toReal : ℂ)⁻¹) ^ 2 *
        ∑ c ∈ hFlc.range_finite.toFinset, (μS.real (F ⁻¹' {c}) : ℂ) * c x := by
    intro x
    rw [kernelAlphaChi_self_eq hHo hAc χ E x, ← hsum x]
  have hterm : ∀ c ∈ hFlc.range_finite.toFinset, Integrable
      (fun q : LeftQuotient A => (μS.real (F ⁻¹' {c}) : ℂ) * c q.out) ν := by
    intro c hc
    refine Integrable.const_mul ?_ _
    have : Nonempty S := ⟨⟨1, by simp [hSdef, N.one_mem]⟩⟩
    have hmem : c ∈ Set.range F := (Set.Finite.mem_toFinset hFlc.range_finite).mp hc
    have hrep : F (Function.invFun F c) = c := Function.invFun_eq hmem
    rw [← hrep]
    exact (hP _).const_mul _
  have hint := (integrable_finsetSum _ hterm).const_mul
    ((((μG.comap H.subtype Set.univ).toReal : ℂ)⁻¹) ^ 2)
  simp_rw [hdiag]
  exact hint.re

end Diagonal

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local instance rationalKernelDiagonalSecondCountable :
    SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

/-- **The pairing input of the VIII.4.1 diagonal.** For every right-invariant `muA`, every
compatible quotient measure `muQ` on `A_G(F) \ G(F)` and every `a ∈ A_G(F)`, the conjugation
pairing of `E` with the characteristic function of `H a`, read at `q̇⁻¹`, is integrable. -/
def RationalLevelKernelPairingIntegrable (muA : Measure (rationalPoints.map s).range)
    (muG : Measure (rationalPoints G)) (H : OpenSubgroup (rationalPoints G))
    (E : RationalSchwartzSpace hKc hPK ρ) : Prop :=
  ∀ [muA.IsMulRightInvariant] [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)),
    IsCompatible (rationalPoints.map s).range muG muA muQ →
    ∀ a : (rationalPoints.map s).range, Integrable (fun q : LeftQuotient (rationalPoints.map s).range =>
      conjugationPairing muG (E : rationalPoints G → ℂ)
        (rightCosetIndicator H.toSubgroup (a : rationalPoints G)) (q.out)⁻¹) muQ

/-- **The diagonal prerequisite of the kernel step from the pairing input.** For connected
reductive `G`, a compact open `H` on which `χ` is trivial on `A_G(F) ∩ H`, a Haar measure
`muG` (right invariant by `rationalHaar_isMulRightInvariant`) and `E` with the properties of `°e_H`, the pairing input gives
`RationalLevelKernelDiagonalIntegrable`. -/
theorem IsRationalCuspidalLevelKernel.diagonalIntegrable (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    (hχH : ∀ b : (rationalPoints.map s).range, (b : rationalPoints G) ∈ H → χ b = 1)
    {E : RationalSchwartzSpace hKc hPK ρ} (hE : IsRationalCuspidalLevelKernel hKc hPK ρ muG H E)
    (hP : RationalLevelKernelPairingIntegrable hKc hPK ρ muA muG H E) :
    RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E := by
  intro _ _ _ muQ hQ
  have := rationalHaar_isMulRightInvariant hG muG
  have hA : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) :=
    isClosed_range_splitComponent G s hs
  have hAc : (rationalPoints.map s).range ≤ Subgroup.center (rationalPoints G) :=
    hs.isCentralSplitTorus.isCentral.range_le_center
  have : LocallyCompactSpace (rationalPoints.map s).range :=
    hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (rationalPoints.map s).range :=
    inferInstanceAs (SecondCountableTopology
      ((rationalPoints.map s).range : Set (rationalPoints G)))
  have : muA.IsInvInvariant := isInvInvariant_of_le_center hAc muA
  have hcpt := isCompact_splitComponent_inf_commonNormKernel G s hG hs
  have hAN : IsCompact {a : (rationalPoints.map s).range |
      (a : rationalPoints G) ∈ rationalCommonNormKernel G} := by
    rw [Subtype.isCompact_iff]
    convert hcpt using 1
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right,
      exists_eq_right, SetLike.mem_coe, Subgroup.mem_inf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
  exact integrable_kernelAlphaChi_self (μG := muG) (ν := muQ) H.isOpen hAc hχH
    (isOpen_rationalCommonNormKernel G)
    (compactSubgroup_le_rationalCommonNormKernel G H.toSubgroup hHc) hAN
    hE.eq_zero_of_not_mem (hP muQ hQ)

end Rational

end Langlands.HarishChandraSchwartz
