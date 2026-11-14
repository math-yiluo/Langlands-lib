import Langlands.Representation.Plancherel.DynamicOppositeContragredientScalar
import Langlands.Representation.Induction.CompactPairingDuality
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction

/-! # Reduction of `j(π̌) = j(π)` to the duality adjunction

Waldspurger 2003, IV.3 (2) (printed p.286) deduces `j(π̌) = j(π)` from the adjunction
IV.1 (11) (printed p.283) `⟨J_{P'|P}(π) f, f̌'⟩ = ⟨f, J_{P|P'}(π̌) f̌'⟩`. This module proves that
deduction for the Library's actual opposite standard integrals: the target
`ConditionalDynamicOppositeDualAdjunctionStatement` (the adjunction on the convergence
domains) implies the target `ConditionalDynamicOppositeContragredientScalarStatement`
(`j_P(Ǎ ⊗ z⁻¹) = j_P(A ⊗ z)` for the canonical scalar `conditionalCanonicalRationalScalar`).
Neither target is proved here.

The proof has three parts.

* The compact-picture duality pairing `⟨φ, φ̌⟩ = ∫_K φ̌(k)(φ(k)) dk` is bilinear
  (`compactPictureDualBilin`) and nondegenerate in the weak sense needed: if `A ≠ 0`, some pair
  of sections has nonzero pairing (`exists_compactPictureDualPairing_ne_zero`). The two sections
  are restrictions to `K` of normalized induced functions supported on `P L` for a small compact
  open subgroup `L ≤ K`, taking values `a` and `λ` with `λ(a) ≠ 0` on `L`.
* For rationally continued operator families, an adjunction on a nonempty open set persists to
  all regular points (`continuedOperator_dualAdjoint`), and two such adjunctions identify the
  fraction extracted from the contragredient composite with the inverted fraction extracted from
  the original composite (`continuedCompositeRationalScalar_dual`).
* The canonical scalar is an extracted fraction for every normalized coefficient
  (`conditionalCanonicalRationalScalar_eq_extraction`); extracting with the vectors and
  functionals of a nonzero pairing gives the reduction
  `conditionalDynamicOppositeContragredientScalar_of_dualAdjunction`.
-/

noncomputable section

universe u uG uV uW uV' uW'

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### The compact-picture duality pairing is bilinear and nondegenerate -/

section Pairing

open Aubert.General Induction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The integrand of the duality pairing is locally constant on the compact group `K`, hence
integrable for the Haar probability. -/
theorem compactPictureDualPairing_integrable (A : SmoothRep.{0, uG, uV} ℂ M)
    (φ : CompactInductionPicture h K A)
    (φ' : CompactInductionPicture h K A.contragredient) :
    Integrable (fun k : K => smoothDualPairing A.representation
      (Induction.eval (P.comap K.toSubgroup.subtype)
        (compactPictureInducingRepresentation h K A.contragredient) φ' k)
      (Induction.eval (P.comap K.toSubgroup.subtype)
        (compactPictureInducingRepresentation h K A) φ k))
      (CompactInduction.measure K hK) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsProbabilityMeasure (CompactInduction.measure K hK) :=
    CompactInduction.measure_isProbability K hK
  exact (bilinearPairing_isLocallyConstant (P.comap K.toSubgroup.subtype) _ _
    (smoothDualPairing A.representation) φ' φ).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The compact-picture duality pairing `⟨φ, φ̌⟩ = ∫_K φ̌(k)(φ(k)) dk` as a bilinear form. -/
def compactPictureDualBilin (A : SmoothRep.{0, uG, uV} ℂ M) :
    CompactInductionPicture h K A →ₗ[ℂ]
      CompactInductionPicture h K A.contragredient →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (compactPictureDualPairing h K hK A)
    (fun φ₁ φ₂ φ' => by
      unfold compactPictureDualPairing
      change (∫ k : K, smoothDualPairing A.representation
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A.contragredient) φ' k)
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A) φ₁ k +
         Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A) φ₂ k)
          ∂CompactInduction.measure K hK) = _
      simp_rw [map_add]
      exact integral_add (compactPictureDualPairing_integrable h K hK A φ₁ φ')
        (compactPictureDualPairing_integrable h K hK A φ₂ φ'))
    (fun c φ φ' => by
      unfold compactPictureDualPairing
      change (∫ k : K, smoothDualPairing A.representation
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A.contragredient) φ' k)
        (c • Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A) φ k)
          ∂CompactInduction.measure K hK) = _
      simp_rw [map_smul]
      exact integral_smul c _)
    (fun φ φ'₁ φ'₂ => by
      unfold compactPictureDualPairing
      rw [← integral_add (compactPictureDualPairing_integrable h K hK A φ φ'₁)
        (compactPictureDualPairing_integrable h K hK A φ φ'₂)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      exact LinearMap.congr_fun ((smoothDualPairing A.representation).map_add
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A.contragredient) φ'₁ k)
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A.contragredient) φ'₂ k))
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A) φ k))
    (fun c φ φ' => by
      unfold compactPictureDualPairing
      rw [← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      exact LinearMap.congr_fun ((smoothDualPairing A.representation).map_smul c
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A.contragredient) φ' k))
        (Induction.eval (P.comap K.toSubgroup.subtype)
          (compactPictureInducingRepresentation h K A) φ k))

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The bilinear form evaluates to the pairing. -/
@[simp]
theorem compactPictureDualBilin_apply (A : SmoothRep.{0, uG, uV} ℂ M)
    (φ : CompactInductionPicture h K A)
    (φ' : CompactInductionPicture h K A.contragredient) :
    compactPictureDualBilin h K hK A φ φ' = compactPictureDualPairing h K hK A φ φ' := rfl

variable [T2Space G]

omit [SecondCountableTopology G] in
/-- **Nondegeneracy.** If `A` has a nonzero vector, some compact-picture section for `A` pairs
nontrivially with some compact-picture section for `Ǎ`. Both sections are restrictions of
normalized induced functions that vanish off `P L` and take the values `a` and `λ` (with
`λ(a) ≠ 0`) on `L`, for a small compact open subgroup `L ≤ K`. The double coset is based at `1`,
so no right translation of the integral, unimodularity of `G` or modulus relation is used. -/
theorem exists_compactPictureDualPairing_ne_zero
    (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (A : SmoothRep.{0, uG, uV} ℂ M) (a : A) (ha : a ≠ 0) :
    ∃ (φ : CompactInductionPicture h K A)
      (φ' : CompactInductionPicture h K A.contragredient),
      compactPictureDualPairing h K hK A φ φ' ≠ 0 := by
  obtain ⟨lam, hlam⟩ := exists_smoothDual_ne_zero
    (compactOpenCofinal_of_isClosed (h.isClosed_levi hP hm)) A.representation A.isSmooth a ha
  obtain ⟨Ha, hHa⟩ := A.isSmooth a
  obtain ⟨Hl, hHl⟩ := lam.property
  have hlamH : lam ∈ fixedVectors (smoothContragredient A.representation) Hl.toSubgroup :=
    fun k => Subtype.ext (hHl k)
  have hχ := HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer
  obtain ⟨Ha', hHa'⟩ := exists_twist_comp_fixed P h.projection hm
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer) hχ A.representation a Ha hHa
  obtain ⟨Hl', hHl'⟩ := exists_twist_comp_fixed P h.projection hm
    (HaarModulus.closedHalfCharacter U hU P h.le_normalizer) hχ
    (smoothContragredient A.representation) lam Hl hlamH
  obtain ⟨L₁, -, -, hwa₁⟩ := exists_compact_conj_fixed P
    (inducingRepresentation h hU A) a Ha' hHa' 1 K
  obtain ⟨L, hL, hLL₁, hwl⟩ := exists_compact_conj_fixed P
    (inducingRepresentation h hU A.contragredient) lam Hl' hHl' 1 L₁
  have hwa : a ∈ fixedVectors (inducingRepresentation h hU A)
      (conjOpenSubgroup P L 1).toSubgroup := fun p =>
    hwa₁ ⟨p.1, mem_conjOpenSubgroup.mpr (hLL₁ (mem_conjOpenSubgroup.mp p.2))⟩
  let f : (normalizedInductionFunctor h hU).obj A :=
    (compactDoubleCosetSection P (inducingRepresentation h hU A) L hL 1 a hwa).val
  let f' : (normalizedInductionFunctor h hU).obj A.contragredient :=
    (compactDoubleCosetSection P (inducingRepresentation h hU A.contragredient)
      L hL 1 lam hwl).val
  refine ⟨normalizedInductionCompactEquiv h K hU hP hK hPK A f,
    normalizedInductionCompactEquiv h K hU hP hK hPK A.contragredient f', ?_⟩
  let ψ : G → ℂ := fun y => smoothDualPairing A.representation
    (eval P (inducingRepresentation h hU A.contragredient) f' y)
    (eval P (inducingRepresentation h hU A) f y)
  have hcov : ∀ (q : P) (x : G), ψ ((q : G) * x) =
      (((HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0) : ℝ) : ℂ) *
        ψ x := by
    intro q x
    have h1 := dualPairing_covariant P h.projection
      (HaarModulus.closedHalfCharacter U hU P h.le_normalizer) A.representation f' f q x
    rw [closedHalfCharacter_mul_self h hU q] at h1
    exact h1
  have hloc : IsLocallyConstant ψ :=
    bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing A.representation) f' f
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsProbabilityMeasure (CompactInduction.measure K hK) :=
    CompactInduction.measure_isProbability K hK
  have : (CompactInduction.measure K hK).IsHaarMeasure := CompactInduction.measure_isHaar K hK
  have hint : Integrable (fun k : (K : Subgroup G) => ψ ((k : G) * 1))
      (CompactInduction.measure K hK) :=
    (hloc.continuous.comp (continuous_subtype_val.mul continuous_const))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hne := integral_ne_zero_of_doubleCoset P
    (fun q => HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q)
    (K : Subgroup G) (CompactInduction.measure K hK) ψ hcov 1 hint L
    (smoothDualPairing A.representation lam a) hlam ?_ ?_
  · simp only [mul_one] at hne
    exact hne
  · intro l
    simp only [ψ, f, f']
    rw [compactDoubleCosetSection_apply_mul]
    exact congrArg (fun x => smoothDualPairing A.representation x a)
      (compactDoubleCosetSection_apply_mul P (inducingRepresentation h hU A.contragredient)
        L hL 1 lam hwl l)
  · intro y hy
    apply compactDoubleCosetSection_mem_of_ne_zero P
      (inducingRepresentation h hU A.contragredient) L hL 1 lam hwl y
    intro h0
    exact hy ((congrArg (fun x => smoothDualPairing A.representation x
      (eval P (inducingRepresentation h hU A) f y)) h0).trans
      ((smoothDualPairing A.representation).map_zero₂ _))

end Pairing

/-! ### Duality persists under rational continuation -/

section ContinuedDual

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W' →ₗ[ℂ] V'}

set_option hygiene false in
local notation "σL" => unramifiedRegularInversion (fun ψ => (rationalNormCharacters L ψ).toMul)

include hp hL in
/-- **Duality persists under continuation.** Let `p` and `q` continue operator families
`A` on `Ω` and `B` on `Λ`, and let `sV`, `sW` be bilinear forms. If
`sW (A w v) w' = sV v (B w⁻¹ w')` for all `w` in a nonempty open `D ⊆ Ω` with `D⁻¹ ⊆ Λ`,
then the same identity holds for the continued operators at every regular `z` of `p` with
`z⁻¹` regular for `q`. -/
theorem continuedOperator_dualAdjoint
    (sV : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (sW : W →ₗ[ℂ] W' →ₗ[ℂ] ℂ)
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hinv : ∀ w ∈ D, w⁻¹ ∈ Λ)
    (hadj : ∀ (w) (hw : w ∈ D) (v : V) (w' : W'),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B ⟨w⁻¹, hinv w hw⟩ w'))
    (z : p.regularRegion) (hz : z.val⁻¹ ∈ q.regularRegion) (v : V) (w' : W') :
    sW (p.continuedOperator z v) w' = sV v (q.continuedOperator ⟨_, hz⟩ w') := by
  obtain ⟨a1, ha1⟩ := (isPolynomialOn_scalar_iff _).mp
    ((p.polynomial v).linearMap (sW.flip w'))
  obtain ⟨a2, ha2⟩ := (isPolynomialOn_scalar_iff _).mp
    ((q.polynomial w').linearMap (sV v))
  have hr : σL q.denominator * a1 - p.denominator * σL a2 = 0 := by
    apply rationalUnramifiedRegular_eq_zero_of_isOpen L hp hL _ hD hne
    intro w hw
    have h1 : sW (p.numerator w v) w' = a1.val w := ha1 ⟨w, Set.mem_univ _⟩
    have h2 : sV v (q.numerator w⁻¹ w') = a2.val w⁻¹ := ha2 ⟨_, Set.mem_univ _⟩
    have hc1 : p.numerator w v = p.denominator.val w • A ⟨w, hDΩ hw⟩ v :=
      LinearMap.congr_fun (p.clears ⟨w, hDΩ hw⟩) v
    have hc2 : q.numerator w⁻¹ w' = q.denominator.val w⁻¹ • B ⟨w⁻¹, hinv w hw⟩ w' :=
      LinearMap.congr_fun (q.clears ⟨w⁻¹, hinv w hw⟩) w'
    have hadj' := hadj w hw v w'
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Pi.sub_apply, Pi.mul_apply,
      unramifiedRegularInversion_apply]
    rw [← h1, ← h2, hc1, hc2]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hadj']
    ring
  have hz0 := congrArg (fun f : unramifiedRegularFunctions _ => f.val z.val) hr
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Pi.sub_apply, Pi.mul_apply,
    unramifiedRegularInversion_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at hz0
  have h1 : sW (p.numerator z.val v) w' = a1.val z.val := ha1 ⟨z.val, Set.mem_univ _⟩
  have h2 : sV v (q.numerator z.val⁻¹ w') = a2.val z.val⁻¹ := ha2 ⟨_, Set.mem_univ _⟩
  rw [← h1, ← h2] at hz0
  have hd : p.denominator.val z.val ≠ 0 := z.property
  have he : q.denominator.val z.val⁻¹ ≠ 0 := hz
  change sW ((p.denominator.val z.val)⁻¹ • p.numerator z.val v) w' =
    sV v ((q.denominator.val z.val⁻¹)⁻¹ • q.numerator z.val⁻¹ w')
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hz0

end ContinuedDual


/-- Inversion of the parameter preserves nonzero regular functions. -/
theorem unramifiedRegularInversion_ne_zero {G : Type uG} [Group G] [TopologicalSpace G]
    {I : Type*} (ν : I → (G →* ℝ≥0ˣ)) {b : unramifiedRegularFunctions ν} (hb : b ≠ 0) :
    unramifiedRegularInversion ν b ≠ 0 := fun h0 => hb (by
  rw [← unramifiedRegularInversion_unramifiedRegularInversion ν b, h0, map_zero])

/-! ### Recognizing an inverted fraction from values -/

section Fraction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)

set_option hygiene false in
local notation "RL" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters L ψ).toMul)

set_option hygiene false in
local notation "FL" => rationalUnramifiedFunctionField L hp hL

set_option hygiene false in
local notation "σL" => unramifiedRegularInversion (fun ψ => (rationalNormCharacters L ψ).toMul)

include hp hL in
/-- A regular identity `a'(w) b(w⁻¹) = a(w⁻¹) b'(w)`, known wherever a fixed nonzero regular
function `N` does not vanish, holds in the ring: `a' σ(b) = σ(a) b'`. -/
theorem mul_unramifiedRegularInversion_eq_of_values (a b a' b' N : RL) (hN : N ≠ 0)
    (h : ∀ w, N.val w ≠ 0 → a'.val w * b.val w⁻¹ = a.val w⁻¹ * b'.val w) :
    a' * σL b = σL a * b' := by
  let := rationalUnramifiedRegularFunctions_isDomain L hp hL
  have hring : (a' * σL b - σL a * b') * N = 0 := by
    apply Subtype.ext
    funext w
    change (a'.val w * b.val w⁻¹ - a.val w⁻¹ * b'.val w) * N.val w = 0
    by_cases hw : N.val w = 0
    · rw [hw, mul_zero]
    · rw [h w hw, sub_self, zero_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hring).resolve_right hN)

/-- Let `f = a/b` and `f' = a'/b'` be fractions of regular functions with
`a' σ(b) = σ(a) b'`. Then `f'` is `f` composed with inversion of the parameter. -/
theorem eq_rationalUnramifiedFunctionFieldInversion_of_mul_eq (f f' : FL) (a b a' b' : RL)
    (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hf : f = algebraMap RL FL a / algebraMap RL FL b)
    (hf' : f' = algebraMap RL FL a' / algebraMap RL FL b')
    (h2 : a' * σL b = σL a * b') :
    f' = rationalUnramifiedFunctionFieldInversion L hp hL f := by
  have hb'0 : algebraMap RL FL b' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective RL FL)).mpr hb'
  have hσb : σL b ≠ 0 := unramifiedRegularInversion_ne_zero _ hb
  have hσb0 : algebraMap RL FL (σL b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective RL FL)).mpr hσb
  have h3 : algebraMap RL FL a' * algebraMap RL FL (σL b) =
      algebraMap RL FL (σL a) * algebraMap RL FL b' := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, h2]
  rw [hf', hf, map_div₀, rationalUnramifiedFunctionFieldInversion_algebraMap,
    rationalUnramifiedFunctionFieldInversion_algebraMap]
  exact (div_eq_div_iff hb'0 hσb0).mpr h3

end Fraction

/-! ### The extracted coefficient for the contragredient -/

section DualScalar

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {Ω Λ Ω' Λ' : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V} {A' : Ω' → V' →ₗ[ℂ] W'} {B' : Λ' → W' →ₗ[ℂ] V'}

set_option hygiene false in
local notation "σL" => unramifiedRegularInversion (fun ψ => (rationalNormCharacters L ψ).toMul)

include hp hL in
/-- **Pointwise duality of extracted coefficients.** Let `p, q` continue a forward family
`A : V → W` and a reverse family `B : W → V`, and `p', q'` continue a forward family
`A' : V' → W'` and a reverse family `B' : W' → V'`. Let `sV`, `sW` be bilinear pairings of
`V` with `V'` and of `W` with `W'` satisfying the two adjunctions
`sW (A w v) w' = sV v (B' w⁻¹ w')` on a nonempty open `D` and
`sV (B w u) v' = sW u (A' w⁻¹ v')` on a nonempty open `E`. For `ℓ = c sV(·, v')` and
`ℓ' = c sV(v, ·)`, the coefficient of `q ∘ p` extracted by `v, ℓ` at `z` equals the coefficient
of `q' ∘ p'` extracted by `v', ℓ'` at `z⁻¹`. -/
theorem continuedCompositeScalar_dual
    (sV : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (sW : W →ₗ[ℂ] W' →ₗ[ℂ] ℂ)
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    (p' : RationalOperatorContinuationData Ω' A')
    (q' : RationalOperatorContinuationData Λ' B')
    {D E : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω) (hinvD : ∀ w ∈ D, w⁻¹ ∈ Λ')
    (hadjD : ∀ (w) (hw : w ∈ D) (v : V) (w' : W'),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B' ⟨w⁻¹, hinvD w hw⟩ w'))
    (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ) (hinvE : ∀ w ∈ E, w⁻¹ ∈ Ω')
    (hadjE : ∀ (w) (hw : w ∈ E) (u : W) (v' : V'),
      sV (B ⟨w, hEΛ hw⟩ u) v' = sW u (A' ⟨w⁻¹, hinvE w hw⟩ v'))
    (v : V) (v' : V') (c : ℂ) (ℓ : V →ₗ[ℂ] ℂ) (ℓ' : V' →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, ℓ x = c * sV x v') (hℓ' : ∀ x, ℓ' x = c * sV v x)
    (z : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (h1 : z ∈ p.regularRegion) (h2 : z ∈ q.regularRegion)
    (h3 : z⁻¹ ∈ p'.regularRegion) (h4 : z⁻¹ ∈ q'.regularRegion) :
    p.continuedCompositeScalar q v ℓ ⟨z, h1, h2⟩ =
      p'.continuedCompositeScalar q' v' ℓ' ⟨z⁻¹, h3, h4⟩ := by
  change ℓ (q.continuedOperator ⟨z, h2⟩ (p.continuedOperator ⟨z, h1⟩ v)) =
    ℓ' (q'.continuedOperator ⟨z⁻¹, h4⟩ (p'.continuedOperator ⟨z⁻¹, h3⟩ v'))
  rw [hℓ, hℓ']
  exact congrArg (c * ·)
    ((continuedOperator_dualAdjoint L hp hL sW sV q p' hE hneE hEΛ hinvE hadjE ⟨z, h2⟩ h3
      (p.continuedOperator ⟨z, h1⟩ v) v').trans
    (continuedOperator_dualAdjoint L hp hL sV sW p q' hD hneD hDΩ hinvD hadjD ⟨z, h1⟩ h4
      v (p'.continuedOperator ⟨z⁻¹, h3⟩ v')))

include hp hL in
/-- **Duality of extracted fractions.** In the situation of `continuedCompositeScalar_dual`,
the fraction extracted from `q' ∘ p'` by `v', ℓ'` is the fraction extracted from `q ∘ p` by
`v, ℓ` composed with inversion of the parameter. -/
theorem continuedCompositeRationalScalar_dual
    (sV : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (sW : W →ₗ[ℂ] W' →ₗ[ℂ] ℂ)
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    (p' : RationalOperatorContinuationData Ω' A')
    (q' : RationalOperatorContinuationData Λ' B')
    {D E : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hneD : D.Nonempty) (hDΩ : D ⊆ Ω) (hinvD : ∀ w ∈ D, w⁻¹ ∈ Λ')
    (hadjD : ∀ (w) (hw : w ∈ D) (v : V) (w' : W'),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B' ⟨w⁻¹, hinvD w hw⟩ w'))
    (hE : IsOpen E) (hneE : E.Nonempty) (hEΛ : E ⊆ Λ) (hinvE : ∀ w ∈ E, w⁻¹ ∈ Ω')
    (hadjE : ∀ (w) (hw : w ∈ E) (u : W) (v' : V'),
      sV (B ⟨w, hEΛ hw⟩ u) v' = sW u (A' ⟨w⁻¹, hinvE w hw⟩ v'))
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) (hΩ' : Ω'.Nonempty) (hΛ' : Λ'.Nonempty)
    (v : V) (v' : V') (c : ℂ) (ℓ : V →ₗ[ℂ] ℂ) (ℓ' : V' →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, ℓ x = c * sV x v') (hℓ' : ∀ x, ℓ' x = c * sV v x) :
    continuedCompositeRationalScalar L hp hL p' q' hΩ' hΛ' v' ℓ' =
      rationalUnramifiedFunctionFieldInversion L hp hL
        (continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ℓ) := by
  have := rationalUnramifiedRegularFunctions_isDomain L hp hL
  exact (continuedCompositeRationalScalar_spec L hp hL p q hΩ hΛ v ℓ).elim fun a1 h =>
  h.elim fun b1 h1 =>
  (continuedCompositeRationalScalar_spec L hp hL p' q' hΩ' hΛ' v' ℓ').elim fun a2 h' =>
  h'.elim fun b2 h2 =>
  eq_rationalUnramifiedFunctionFieldInversion_of_mul_eq L hp hL _ _ a1 b1 a2 b2 h1.1 h2.1
    h1.2.2.1 h2.2.2.1
    (mul_unramifiedRegularInversion_eq_of_values L hp hL a1 b1 a2 b2
      (σL p.denominator * σL q.denominator * p'.denominator * q'.denominator)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (unramifiedRegularInversion_ne_zero _ (p.denominator_ne_zero hΩ))
        (unramifiedRegularInversion_ne_zero _ (q.denominator_ne_zero hΛ)))
        (p'.denominator_ne_zero hΩ')) (q'.denominator_ne_zero hΛ'))
      (fun w hw => by
        have hw' : p.denominator.val w⁻¹ * q.denominator.val w⁻¹ *
            p'.denominator.val w * q'.denominator.val w ≠ 0 := hw
        have r1 : w⁻¹ ∈ p.regularRegion := left_ne_zero_of_mul (left_ne_zero_of_mul
          (left_ne_zero_of_mul hw'))
        have r2 : w⁻¹ ∈ q.regularRegion := right_ne_zero_of_mul (left_ne_zero_of_mul
          (left_ne_zero_of_mul hw'))
        have r3 : w⁻¹⁻¹ ∈ p'.regularRegion := by
          rw [inv_inv]
          exact right_ne_zero_of_mul (left_ne_zero_of_mul hw')
        have r4 : w⁻¹⁻¹ ∈ q'.regularRegion := by
          rw [inv_inv]
          exact right_ne_zero_of_mul hw'
        have hk := (h1.2.2.2 ⟨w⁻¹, r1, r2⟩).symm.trans
          ((continuedCompositeScalar_dual L hp hL sV sW p q p' q' hD hneD hDΩ hinvD hadjD
            hE hneE hEΛ hinvE hadjE v v' c ℓ ℓ' hℓ hℓ' w⁻¹ r1 r2 r3 r4).trans
            (h2.2.2.2 ⟨w⁻¹⁻¹, r3, r4⟩))
        change a1.val w⁻¹ / b1.val w⁻¹ = a2.val w⁻¹⁻¹ / b2.val w⁻¹⁻¹ at hk
        have hb1 := h1.2.1 ⟨w⁻¹, r1, r2⟩
        have hb2 := h2.2.1 ⟨w⁻¹⁻¹, r3, r4⟩
        change b1.val w⁻¹ ≠ 0 at hb1
        change b2.val w⁻¹⁻¹ ≠ 0 at hb2
        rw [div_eq_div_iff hb1 hb2, inv_inv] at hk
        rw [inv_inv] at hb2
        exact hk.symm))

end DualScalar

/-! ### The reduction -/

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

/-- The Borel structure on the actual rational points. -/
local instance contragredientReductionPointMeasurable {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    MeasurableSpace (RationalPoint F G.X) :=
  borel _

local instance contragredientReductionPointBorel {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    BorelSpace (RationalPoint F G.X) :=
  ⟨rfl⟩

/-- A vector with a normalized coefficient is nonzero. -/
theorem ne_zero_of_coefficient_eq_one {X : Type uV} [AddCommGroup X] [Module ℂ X]
    {v : X} {ℓ : X →ₗ[ℂ] ℂ} (h : ℓ v = 1) : v ≠ 0 := fun h0 => by
  rw [h0, map_zero] at h
  exact zero_ne_one h

/-- **Reduction (Waldspurger IV.3 (2) from IV.1 (11)).** The duality adjunction on the
convergence domains implies `j_P(Ǎ ⊗ z⁻¹) = j_P(A ⊗ z)` for the canonical scalar. -/
theorem conditionalDynamicOppositeContragredientScalar_of_dualAdjunction
    (H : ConditionalDynamicOppositeDualAdjunctionStatement.{u, uV}) :
    ConditionalDynamicOppositeContragredientScalarStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi p' q' DForward' DReverse' hDForward' hneForward' hDForwardΩ'
    hDReverse' hneReverse' hDReverseΩ' D' hD' hne' hi' hinvForward hinvReverse
  refine (exists_normalized_compactCoefficient (χ := χ) (hG := hG) (K := K) (hK := hK)
    (hPK := hPK) (A := A) (hne := hne) (hi := hi)).elim fun v hv => hv.elim fun ℓ0 hℓ0 => ?_
  refine (Induction.exists_eval_ne_zero _ _ v
    (ne_zero_of_coefficient_eq_one hℓ0)).elim fun k hk => ?_
  refine (exists_compactPictureDualPairing_ne_zero (decomposition χ) K hK
    (radical_isClosed χ) (parabolic_isClosed χ) (projection_continuous χ) hPK A _ hk).elim
    fun φ hφ => hφ.elim fun φ' hc0 => ?_
  exact (conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK
      A.contragredient p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse'
      hDReverseΩ' hD' hne' hi' φ'
      ((compactPictureDualPairing (decomposition χ) K hK A φ φ')⁻¹ •
        compactPictureDualBilin (decomposition χ) K hK A φ)
      (inv_mul_cancel₀ hc0)).trans
    ((continuedCompositeRationalScalar_dual (parameterScheme χ)
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
      (compactPictureDualBilin (decomposition χ) K hK A)
      (compactPictureDualBilin (oppositeDecomposition χ) K hK A) p q p' q'
      hDForward hneForward hDForwardΩ hinvForward
      (fun w hw u u' => (H χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A).1
        ⟨w, hDForwardΩ hw⟩ (hinvForward w hw) u u')
      hDReverse hneReverse hDReverseΩ hinvReverse
      (fun w hw u u' => (H χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A).2
        ⟨w, hDReverseΩ hw⟩ (hinvReverse w hw) u u')
      (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ)
      (hneForward'.mono hDForwardΩ') (hneReverse'.mono hDReverseΩ') φ φ'
      (compactPictureDualPairing (decomposition χ) K hK A φ φ')⁻¹
      ((compactPictureDualPairing (decomposition χ) K hK A φ φ')⁻¹ •
        (compactPictureDualBilin (decomposition χ) K hK A).flip φ')
      ((compactPictureDualPairing (decomposition χ) K hK A φ φ')⁻¹ •
        compactPictureDualBilin (decomposition χ) K hK A φ)
      (fun _ => rfl) (fun _ => rfl)).trans
    (congrArg (rationalUnramifiedFunctionFieldInversion (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG))
      (conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK
        A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi φ
        ((compactPictureDualPairing (decomposition χ) K hK A φ φ')⁻¹ •
          (compactPictureDualBilin (decomposition χ) K hK A).flip φ')
        (inv_mul_cancel₀ hc0)).symm))

end Langlands.Plancherel
