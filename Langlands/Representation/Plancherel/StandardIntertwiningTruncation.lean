import Langlands.Representation.Plancherel.StandardIntertwiningCovariance
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.BlockCompressionProof

/-! # Truncations of the standard integral and Casselman compression

Set integrals of the actual standard integrand over measurable subsets of the
radical quotient. A Levi element shifts the truncation set by quotient
conjugation, target-radical translations preserve stable truncations, and
monotone exhausting truncations converge to the full integral. Under an Iwahori
contraction, compression by a contracting element realizes these shifts on
fixed vectors.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal ENNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

section Truncation

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- The scalar standard integral over one subset of the radical quotient. -/
def truncatedIntegral (C : Set (QuotientSpace (U := U) U')) (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual A.representation) : ℂ :=
  ∫ q in C, ℓ.val (integrand h hU U' A g f q) ∂ν

/-- Every scalar test of a domain vector is integrable. -/
theorem integrable_scalar_of_mem_domain
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A}
    (hf : f ∈ domain h hU U' A ν) (g : G) (ℓ : SmoothDual A.representation) :
    Integrable (fun q => ℓ.val (integrand h hU U' A g f q)) ν := by
  obtain ⟨Jf, hJf⟩ := (mem_domain h hU U' A ν f).mp hf
  exact (hJf g ℓ).1

/-- Truncation is linear on the actual domain. -/
def truncatedFunctional (C : Set (QuotientSpace (U := U) U')) (g : G)
    (ℓ : SmoothDual A.representation) : domain h hU U' A ν →ₗ[ℂ] ℂ where
  toFun f := truncatedIntegral h hU U' A ν C g f.val ℓ
  map_add' f f' := by
    change ∫ q in C, ℓ.val (integrand h hU U' A g (f.val + f'.val) q) ∂ν =
      truncatedIntegral h hU U' A ν C g f.val ℓ + truncatedIntegral h hU U' A ν C g f'.val ℓ
    simp only [map_add, Pi.add_apply]
    exact integral_add
      (integrable_scalar_of_mem_domain h hU U' A ν f.property g ℓ).integrableOn
      (integrable_scalar_of_mem_domain h hU U' A ν f'.property g ℓ).integrableOn
  map_smul' c f := by
    change ∫ q in C, ℓ.val (integrand h hU U' A g (c • f.val) q) ∂ν =
      c • truncatedIntegral h hU U' A ν C g f.val ℓ
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _

theorem truncatedIntegral_smul_functional (C : Set (QuotientSpace (U := U) U')) (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (c : ℂ) (ℓ : SmoothDual A.representation) :
    truncatedIntegral h hU U' A ν C g f (c • ℓ) =
      c * truncatedIntegral h hU U' A ν C g f ℓ := by
  simp only [truncatedIntegral, SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

/-- Monotone exhausting truncations converge to the selected integral. -/
theorem tendsto_truncatedIntegral (hM : IsClosed (M : Set G))
    (f : domain h hU U' A ν) (g : G) (ℓ : SmoothDual A.representation)
    {C : ℕ → Set (QuotientSpace (U := U) U')} (hmeas : ∀ n, MeasurableSet (C n))
    (hmono : Monotone C) (hunion : ⋃ n, C n = Set.univ) :
    Tendsto (fun n => truncatedIntegral h hU U' A ν (C n) g f.val ℓ) atTop
      (𝓝 (ℓ.val (operator h hU U' A ν hM f g))) := by
  rw [operator_eval]
  have ht := tendsto_setIntegral_of_monotone hmeas hmono
    (integrable_scalar_of_mem_domain h hU U' A ν f.property g ℓ).integrableOn
  rw [hunion, setIntegral_univ] at ht
  exact ht

variable [MeasurableSpace U'] [MeasurableSpace (U.subgroupOf U')]
  [BorelSpace (U.subgroupOf U')] [BorelSpace (QuotientSpace (U := U) U')]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U')) [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)

include hν in
/-- A target-radical translation preserving the truncation set preserves the
truncated integral at the identity. -/
theorem truncatedIntegral_unipotent (C : Set (QuotientSpace (U := U) U')) (u : U')
    (hC : QuotientIntegration.rightTranslate (U.subgroupOf U') u ⁻¹' C = C)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual A.representation) :
    truncatedIntegral h hU U' A ν C 1
        (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          (u : G) f) ℓ =
      truncatedIntegral h hU U' A ν C 1 f ℓ := by
  have hfun : (fun q => ℓ.val (integrand h hU U' A 1
      (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
        (u : G) f) q)) =
      fun q => ℓ.val (integrand h hU U' A 1 f
        (QuotientIntegration.rightTranslate (U.subgroupOf U') u q)) := by
    funext q
    rw [integrand_right_action, one_mul, ← mul_one (u : G), integrand_unipotent_mul]
  unfold truncatedIntegral
  rw [hfun]
  conv_lhs => rw [← hC]
  exact (hν.right_invariant u).setIntegral_preimage_emb
    (QuotientIntegration.rightTranslate (U.subgroupOf U') u).measurableEmbedding
    (fun q => ℓ.val (integrand h hU U' A 1 f q)) C

end Truncation

section LeviShift

variable (hMU' : M ≤ Subgroup.normalizer (U' : Set G))
  [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)

/-- The actual Levi transformation factor of the standard integrand. -/
def leviShiftFactor (m : M) : ℂ :=
  (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
    ((quotientConjugationModulus h hU U' hMU' m : ℝ) : ℂ)

include hν in
/-- A Levi element shifts the truncation set by quotient conjugation and the
functional by the actual inducing action. -/
theorem truncatedIntegral_levi (m : M) (C : Set (QuotientSpace (U := U) U'))
    (hC : MeasurableSet C)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual A.representation) :
    truncatedIntegral h hU U' A ν C 1
        (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          (m : G) f) ℓ =
      leviShiftFactor h hU U' hMU' m *
        truncatedIntegral h hU U' A ν (quotientConjugation h U' hMU' m ⁻¹' C) 1 f
          (smoothContragredient A.representation m⁻¹ ℓ) := by
  set φ := quotientConjugation h U' hMU' m
  set ℓm : SmoothDual A.representation := smoothContragredient A.representation m⁻¹ ℓ
  have hℓm (w : A) : ℓm.val w = ℓ.val (A.representation m w) := by
    change ℓ.val (A.representation (m⁻¹)⁻¹ w) = _
    rw [inv_inv]
  have hpt (q : QuotientSpace (U := U) U') :
      ℓ.val (integrand h hU U' A 1
        (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          (m : G) f) q) =
        (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
          ℓm.val (integrand h hU U' A 1 f (φ.symm q)) := by
    rw [integrand_right_action, one_mul, ← mul_one (m : G),
      integrand_levi_mul h hU U' hMU' A, map_smul, hℓm]
    rfl
  have hmeas : MeasurableSet (φ ⁻¹' C) := φ.continuous.measurable hC
  have hind : (fun q => C.indicator
      (fun q' => ℓm.val (integrand h hU U' A 1 f (φ.symm q'))) q) =
      fun q => (φ ⁻¹' C).indicator (fun q' => ℓm.val (integrand h hU U' A 1 f q'))
        (φ.symm q) := by
    funext q
    by_cases hq : q ∈ C
    · have hq' : φ.symm q ∈ φ ⁻¹' C := by
        simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hq
      rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
    · have hq' : φ.symm q ∉ φ ⁻¹' C := by
        simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hq
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
  unfold truncatedIntegral leviShiftFactor
  simp_rw [hpt]
  rw [integral_const_mul, ← integral_indicator hC, hind,
    integral_quotientConjugation_symm h hU U' hMU' ν μU' μI hν m, integral_indicator hmeas,
    mul_assoc]

end LeviShift

section Compression

variable (hMU' : M ≤ Subgroup.normalizer (U' : Set G))
  [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)

/-- Truncation as a linear functional on the whole source, when the actual
domain is the whole source. -/
def truncatedLinear (hfull : domain h hU U' A ν = ⊤)
    (C : Set (QuotientSpace (U := U) U')) (ℓ : SmoothDual A.representation) :
    (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A →ₗ[ℂ] ℂ :=
  (truncatedFunctional h hU U' A ν C 1 ℓ).comp (LinearEquiv.ofTop _ hfull).symm.toLinearMap

omit [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [BorelSpace (QuotientSpace (U := U) U')] in
theorem truncatedLinear_apply (hfull : domain h hU U' A ν = ⊤)
    (C : Set (QuotientSpace (U := U) U')) (ℓ : SmoothDual A.representation)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    truncatedLinear h hU U' A ν hfull C ℓ f = truncatedIntegral h hU U' A ν C 1 f ℓ := rfl

omit [LocallyCompactSpace G] [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')] in
/-- Quotient conjugation intertwines right translations. -/
theorem quotientConjugation_rightTranslate (m : M) (u : U')
    (q : QuotientSpace (U := U) U') :
    quotientConjugation h U' hMU' m (QuotientIntegration.rightTranslate (U.subgroupOf U') u q) =
      QuotientIntegration.rightTranslate (U.subgroupOf U')
        (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩ u)
        (quotientConjugation h U' hMU' m q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    change Quotient.mk _ (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩ (x * u)) =
      Quotient.mk _ (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩ x *
        HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩ u)
    rw [map_mul]

/-- Truncation sets stable under the target-radical part of a compact open
subgroup. -/
def IsRadicalStable (H : OpenSubgroup G) (C : Set (QuotientSpace (U := U) U')) : Prop :=
  ∀ u : U', (u : G) ∈ H → QuotientIntegration.rightTranslate (U.subgroupOf U') u ⁻¹' C = C

variable {H : OpenSubgroup G} {O : Subgroup G} {a : G}

/-- The contracting element as an element of the Levi subgroup. -/
def contractionLevi (hI : Jacquet.IsIwahoriContraction H U' M O a) : M :=
  ⟨a, hI.mem_levi⟩

omit [LocallyCompactSpace G] [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')] in
theorem isRadicalStable_preimage (hI : Jacquet.IsIwahoriContraction H U' M O a)
    {C : Set (QuotientSpace (U := U) U')} (hC : IsRadicalStable U' H C) :
    IsRadicalStable U' H (quotientConjugation h U' hMU' (contractionLevi U' hI) ⁻¹' C) := by
  intro u hu
  ext q
  simp only [Set.mem_preimage]
  rw [quotientConjugation_rightTranslate]
  have hu' : (HaarModulus.normalizerConj U'
      ⟨(contractionLevi U' hI : G), hMU' (contractionLevi U' hI).property⟩ u : G) ∈ H :=
    (hI.upper (u : G) ⟨hu, u.property⟩).1
  rw [← Set.mem_preimage (f := QuotientIntegration.rightTranslate (U.subgroupOf U') _),
    hC _ hu']

variable (hfull : domain h hU U' A ν = ⊤) (hH : IsCompact (H : Set G))
  (hρ : IsSmooth ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation)

omit [LocallyCompactSpace U'] [BorelSpace U'] [T2Space G] [IsHaarMeasure μU'] [μU'.Regular]
  [IsMulRightInvariant μU'] [IsHaarMeasure μI] [μI.Regular] in
include hν hfull in
/-- On fixed vectors, compression by the contracting element has the same
radical-stable truncations as translation by it. -/
theorem truncatedIntegral_compressedAction (hI : Jacquet.IsIwahoriContraction H U' M O a)
    {C : Set (QuotientSpace (U := U) U')} (hC : IsRadicalStable U' H C)
    (v : fixedVectors ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
      H.toSubgroup)
    (ℓ : SmoothDual A.representation) :
    truncatedIntegral h hU U' A ν C 1
        (Jacquet.compressedAction
          ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          hρ H hH a v :
          (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) ℓ =
      truncatedIntegral h hU U' A ν C 1
        (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation a v) ℓ := by
  rw [← truncatedLinear_apply h hU U' A ν hfull, ← truncatedLinear_apply h hU U' A ν hfull,
    Jacquet.compressedAction_apply]
  apply Jacquet.map_averageMap_of_forall_eq
  intro k
  obtain ⟨u, hu, hk⟩ := Jacquet.exists_upper_translate
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation H U' M O
    hI.factor a (fun l hl => (hI.lower l hl).1) (fun m hm => (hI.levi m hm).1)
    v.val v.property k.val k.property
  rw [hk, truncatedLinear_apply]
  exact truncatedIntegral_unipotent h hU U' A ν μU' μI hν C ⟨u, hu.2⟩ (hC ⟨u, hu.2⟩ hu.1) _ ℓ

include hν hfull in
/-- Iterated compression shifts radical-stable truncations by iterated
quotient conjugation, with one actual Levi factor per step. -/
theorem truncatedIntegral_compressedAction_pow (hI : Jacquet.IsIwahoriContraction H U' M O a)
    (v : fixedVectors ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
      H.toSubgroup) :
    ∀ (n : ℕ) (C : Set (QuotientSpace (U := U) U')), MeasurableSet C →
      IsRadicalStable U' H C → ∀ ℓ : SmoothDual A.representation,
      truncatedIntegral h hU U' A ν C 1
          (((Jacquet.compressedAction
            ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
            hρ H hH a) ^ n)
            v : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) ℓ =
        leviShiftFactor h hU U' hMU' (contractionLevi U' hI) ^ n *
          truncatedIntegral h hU U' A ν
            ((fun s => quotientConjugation h U' hMU' (contractionLevi U' hI) ⁻¹' s)^[n] C) 1
            v.val
            ((smoothContragredient A.representation (contractionLevi U' hI)⁻¹ ^ n) ℓ) := by
  intro n
  induction n with
  | zero =>
    intro C _ _ ℓ
    simp
  | succ n ih =>
    intro C hCm hC ℓ
    rw [pow_succ', Module.End.mul_apply,
      truncatedIntegral_compressedAction h hU U' A ν μU' μI hν hfull hH hρ hI hC]
    have hlevi := truncatedIntegral_levi h hU U' A hMU' ν μU' μI hν
      (contractionLevi U' hI) C hCm
      ((((Jacquet.compressedAction
        ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
        hρ H hH a) ^ n)
        v : _) : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) ℓ
    change truncatedIntegral h hU U' A ν C 1
      (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
        ((contractionLevi U' hI : M) : G) _) ℓ = _
    rw [hlevi, ih _ ((quotientConjugation h U' hMU' _).continuous.measurable hCm)
      (isRadicalStable_preimage h U' hMU' hI hC), Function.iterate_succ_apply,
      pow_succ (smoothContragredient A.representation _), Module.End.mul_apply, ← mul_assoc,
      ← pow_succ']

end Compression

section Exhaustion

variable (hMU' : M ≤ Subgroup.normalizer (U' : Set G))
  {H : OpenSubgroup G} {O : Subgroup G} {a : G}

/-- The image of the compact part `H ∩ U'` in the radical quotient. -/
def compactRadicalPiece (H : OpenSubgroup G) : Set (QuotientSpace (U := U) U') :=
  Induction.quotientMap (U.subgroupOf U') '' {y : U' | (y : G) ∈ H}

omit [LocallyCompactSpace G] in
theorem isOpen_compactRadicalPiece (H : OpenSubgroup G) :
    IsOpen (compactRadicalPiece (U := U) U' H) :=
  (QuotientIntegration.leftQuotient_isOpenQuotientMap (U.subgroupOf U')).isOpenMap _
    (continuous_subtype_val.isOpen_preimage _ H.isOpen)

omit [LocallyCompactSpace G] in
theorem isRadicalStable_compactRadicalPiece (H : OpenSubgroup G) :
    IsRadicalStable U' H (compactRadicalPiece (U := U) U' H) := by
  intro u hu
  ext q
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨y, hy, hyq⟩
    refine ⟨y * u⁻¹, H.mul_mem hy (H.inv_mem hu), ?_⟩
    have hq : q = QuotientIntegration.rightTranslate (U.subgroupOf U') u⁻¹
        (QuotientIntegration.rightTranslate (U.subgroupOf U') u q) := by
      rw [QuotientIntegration.rightTranslate_mul, mul_inv_cancel,
        QuotientIntegration.rightTranslate_one]
    rw [hq, ← hyq]
    rfl
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y * u, H.mul_mem hy hu, rfl⟩

omit [LocallyCompactSpace G] in
/-- Iterated quotient conjugation by the contracting element is conjugation by
its powers on representatives. -/
theorem quotientConjugation_iterate_mk (hI : Jacquet.IsIwahoriContraction H U' M O a)
    (x : U') (n : ℕ) :
    ∃ y : U', (y : G) = a ^ n * (x : G) * (a ^ n)⁻¹ ∧
      (quotientConjugation h U' hMU' (contractionLevi U' hI))^[n]
          (Induction.quotientMap (U.subgroupOf U') x) =
        Induction.quotientMap (U.subgroupOf U') y := by
  induction n with
  | zero => exact ⟨x, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨y, hy, hq⟩ := ih
    refine ⟨HaarModulus.normalizerConj U'
      ⟨(contractionLevi U' hI : G), hMU' (contractionLevi U' hI).property⟩ y, ?_, ?_⟩
    · rw [HaarModulus.normalizerConj_apply, hy]
      change a * (a ^ n * (x : G) * (a ^ n)⁻¹) * a⁻¹ = _
      group
    · rw [Function.iterate_succ_apply', hq]
      rfl

omit [LocallyCompactSpace G] in
theorem compactRadicalPiece_subset_preimage
    (hI : Jacquet.IsIwahoriContraction H U' M O a) :
    compactRadicalPiece (U := U) U' H ⊆
      quotientConjugation h U' hMU' (contractionLevi U' hI) ⁻¹' compactRadicalPiece U' H := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨HaarModulus.normalizerConj U'
      ⟨(contractionLevi U' hI : G), hMU' (contractionLevi U' hI).property⟩ y,
    (hI.upper (y : G) ⟨hy, y.property⟩).1, rfl⟩

/-- The exhausting truncation sets. -/
def compactRadicalExhaustion (hI : Jacquet.IsIwahoriContraction H U' M O a) (n : ℕ) :
    Set (QuotientSpace (U := U) U') :=
  (fun s => quotientConjugation h U' hMU' (contractionLevi U' hI) ⁻¹' s)^[n]
    (compactRadicalPiece U' H)

omit [LocallyCompactSpace G] in
theorem compactRadicalExhaustion_eq (hI : Jacquet.IsIwahoriContraction H U' M O a) (n : ℕ) :
    compactRadicalExhaustion h U' hMU' hI n =
      (quotientConjugation h U' hMU' (contractionLevi U' hI))^[n] ⁻¹'
        compactRadicalPiece U' H := by
  unfold compactRadicalExhaustion
  exact Set.preimage_iterate_eq.symm ▸ rfl

omit [LocallyCompactSpace G] in
theorem monotone_compactRadicalExhaustion
    (hI : Jacquet.IsIwahoriContraction H U' M O a) :
    Monotone (compactRadicalExhaustion h U' hMU' hI) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [compactRadicalExhaustion_eq, compactRadicalExhaustion_eq, Function.iterate_succ',
    Set.preimage_comp]
  exact Set.preimage_mono (compactRadicalPiece_subset_preimage h U' hMU' hI)

omit [LocallyCompactSpace G] in
theorem iUnion_compactRadicalExhaustion (hI : Jacquet.IsIwahoriContraction H U' M O a) :
    ⋃ n, compactRadicalExhaustion h U' hMU' hI n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨r, hr⟩ := hI.exhaust (x : G) x.property
    obtain ⟨y, hy, hq⟩ := quotientConjugation_iterate_mk h U' hMU' hI x r
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    rw [compactRadicalExhaustion_eq, Set.mem_preimage]
    change (quotientConjugation h U' hMU' (contractionLevi U' hI))^[r]
      (Induction.quotientMap (U.subgroupOf U') x) ∈ _
    rw [hq]
    refine ⟨y, ?_, rfl⟩
    change (y : G) ∈ H
    rw [hy]
    exact hr

end Exhaustion

section Convergence

variable (hMU' : M ≤ Subgroup.normalizer (U' : Set G))
  [LocallyCompactSpace U'] [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')] [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
  (hfull : domain h hU U' A ν = ⊤) {H : OpenSubgroup G} (hH : IsCompact (H : Set G))
  (hρ : IsSmooth ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation)
  {O : Subgroup G} {a : G}

omit [T2Space G] [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] in
theorem leviShiftFactor_ne_zero (m : M) : leviShiftFactor h hU U' hMU' m ≠ 0 := by
  let := (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  apply mul_ne_zero (Units.ne_zero _)
  exact_mod_cast (quotientConjugationModulus_pos h hU U' hMU' m).ne'

/-- The smooth-dual step: inverse Levi factor times the contragredient action
of the contracting element. -/
def dualCompressionShift (hI : Jacquet.IsIwahoriContraction H U' M O a) :
    Module.End ℂ (SmoothDual A.representation) :=
  (leviShiftFactor h hU U' hMU' (contractionLevi U' hI))⁻¹ •
    smoothContragredient A.representation (contractionLevi U' hI)

include hν hfull in
/-- Compression iterates paired with dual shifts are the exhausting truncations. -/
theorem truncatedIntegral_compressedAction_pow_dualShift
    (hI : Jacquet.IsIwahoriContraction H U' M O a)
    (v : fixedVectors ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
      H.toSubgroup) (n : ℕ) (ℓ : SmoothDual A.representation) :
    truncatedIntegral h hU U' A ν (compactRadicalPiece U' H) 1
        (((Jacquet.compressedAction
          ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          hρ H hH a) ^ n) v : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
        ((dualCompressionShift h hU U' A hMU' hI ^ n) ℓ) =
      truncatedIntegral h hU U' A ν (compactRadicalExhaustion h U' hMU' hI n) 1 v.val ℓ := by
  rw [truncatedIntegral_compressedAction_pow h hU U' A hMU' ν μU' μI hν hfull hH hρ hI v n
    _ (isOpen_compactRadicalPiece U' H).measurableSet
    (isRadicalStable_compactRadicalPiece U' H)]
  have hdual : (smoothContragredient A.representation (contractionLevi U' hI)⁻¹ ^ n)
      ((dualCompressionShift h hU U' A hMU' hI ^ n) ℓ) =
      ((leviShiftFactor h hU U' hMU' (contractionLevi U' hI))⁻¹ ^ n) • ℓ := by
    rw [dualCompressionShift, smul_pow, LinearMap.smul_apply, map_smul,
      ← Module.End.mul_apply, ← map_pow, ← map_pow, ← map_mul,
      inv_pow (contractionLevi U' hI) n, inv_mul_cancel,
      map_one, Module.End.one_apply]
  rw [hdual, truncatedIntegral_smul_functional, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (leviShiftFactor_ne_zero h hU U' hMU' _), one_pow, one_mul]
  rfl

include hν hfull in
/-- The compression iterates converge weakly to the actual standard integral. -/
theorem tendsto_compressedTruncation (hM : IsClosed (M : Set G))
    (hI : Jacquet.IsIwahoriContraction H U' M O a)
    (v : fixedVectors ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
      H.toSubgroup) (ℓ : SmoothDual A.representation) :
    Tendsto (fun n => truncatedIntegral h hU U' A ν (compactRadicalPiece U' H) 1
        (((Jacquet.compressedAction
          ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          hρ H hH a) ^ n) v : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
        ((dualCompressionShift h hU U' A hMU' hI ^ n) ℓ)) atTop
      (𝓝 (ℓ.val (operator h hU U' A ν hM ⟨v.val, hfull ▸ Submodule.mem_top⟩ 1))) := by
  simp_rw [truncatedIntegral_compressedAction_pow_dualShift h hU U' A hMU' ν μU' μI hν hfull hH
    hρ hI v]
  exact tendsto_truncatedIntegral h hU U' A ν hM ⟨v.val, hfull ▸ Submodule.mem_top⟩ 1 ℓ
    (fun n => (compactRadicalExhaustion_eq h U' hMU' hI n).symm ▸
      ((Homeomorph.continuous _).iterate n).measurable
        (isOpen_compactRadicalPiece U' H).measurableSet)
    (monotone_compactRadicalExhaustion h U' hMU' hI)
    (iUnion_compactRadicalExhaustion h U' hMU' hI)

end Convergence

end Langlands.Plancherel.StandardIntertwining
