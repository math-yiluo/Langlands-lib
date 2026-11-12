import Langlands.Representation.Hecke.CompactInductionComparison
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Induction.CompactLocalSectionSpanningProof

/-! # Local sections in the range of the elementary comparison -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace H] in
/-- The subgroup stabilizing the coefficient at the identity is compact when
the inducing subgroup is closed. -/
theorem compact_identityCoefficientSubgroup (hH : IsClosed (H : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    IsCompact (Induction.conjOpenSubgroup H K 1 : Set H) := by
  have he : (Induction.conjOpenSubgroup H K 1 : Set H) =
      Subtype.val ⁻¹' (K : Set G) := by
    ext h
    simp [Induction.mem_conjOpenSubgroup]
  rw [he]
  exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The relative modular character is trivial on the compact coefficient
stabilizer at the identity. -/
theorem relativeModularCharacter_identityCoefficient (hH : IsClosed (H : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (h : H)
    (hh : h ∈ Induction.conjOpenSubgroup H K 1) :
    ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) = 1 := by
  have hhG : (h : G) ∈ K := by
    simpa only [inv_one, one_mul, mul_one] using Induction.mem_conjOpenSubgroup.mp hh
  have hΔH := Haar.modularCharacter_eq_one_of_mem_compactOpen
    (Induction.conjOpenSubgroup H K 1) (compact_identityCoefficientSubgroup H hH K hK) hh
  have hΔG := Haar.modularCharacter_eq_one_of_mem_compactOpen K hK (K.inv_mem hhG)
  change ((modularCharacter h : ℝ) : ℂ) * ((modularCharacter ((h : G)⁻¹) : ℝ) : ℂ) = 1
  rw [hΔH, hΔG]
  simp

variable (μH : Measure H) [μH.IsHaarMeasure]

/-- The ambient subgroup indicator normalized by the Haar mass of `H ∩ K`. -/
def compactSectionTest (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    SchwartzBruhat G :=
  ((μH.real (Induction.conjOpenSubgroup H K 1 : Set H) : ℂ)⁻¹) •
    TestFunction.subgroupIndicator K hK

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [LocallyCompactSpace H]
  [μH.IsHaarMeasure] in
@[simp] theorem compactSectionTest_apply (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : G) :
    compactSectionTest H μH K hK x =
      (μH.real (Induction.conjOpenSubgroup H K 1 : Set H) : ℂ)⁻¹ *
        (K : Set G).indicator (fun _ => (1 : ℂ)) x := rfl

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [LocallyCompactSpace H]
  [μH.IsHaarMeasure] in
theorem compactSectionTest_biInvariant (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    compactSectionTest H μH K hK ∈ TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
  (TestFunction.biInvariant K.toSubgroup K.toSubgroup).smul_mem _
    (TestFunction.subgroupIndicator_mem K hK)

omit [T2Space G] [BorelSpace G] [μH.IsHaarMeasure] in
/-- At the identity the comparison subgroup test is exactly the normalized
indicator of the coefficient stabilizer. -/
theorem compactSubgroupTest_sectionTest (hH : IsClosed (H : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    compactSubgroupTest H hH 1 (compactSectionTest H μH K hK) =
      HeckeAlgebra.toTestFunction μH
        (HeckeAlgebra.normalizedIndicator μH (Induction.conjOpenSubgroup H K 1)
          (compact_identityCoefficientSubgroup H hH K hK)) := by
  ext h
  have hmem : h ∈ Induction.conjOpenSubgroup H K 1 ↔ (h : G) ∈ K := by
    simp [Induction.mem_conjOpenSubgroup]
  change ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) *
    compactSectionTest H μH K hK (1⁻¹ * (h : G)) =
      HeckeAlgebra.normalizedIndicator μH (Induction.conjOpenSubgroup H K 1) _ h
  by_cases hh : h ∈ Induction.conjOpenSubgroup H K 1
  · simp [compactSectionTest_apply, HeckeAlgebra.normalizedIndicator_apply,
      hh, hmem.mp hh, relativeModularCharacter_identityCoefficient H hH K hK h hh]
  · simp [compactSectionTest_apply, HeckeAlgebra.normalizedIndicator_apply,
      hh, mt hmem.mpr hh]

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

omit [T2Space G] in
/-- The elementary comparison recovers the prescribed identity value. -/
theorem compactComparisonValue_sectionTest_one (hH : IsClosed (H : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (w : V)
    (hw : w ∈ fixedVectors
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ)
      (Induction.conjOpenSubgroup H K 1).toSubgroup) :
    compactComparisonValue H hH μH ρ hρ (compactSectionTest H μH K hK) w 1 = w := by
  have hwρ : w ∈ fixedVectors ρ (Induction.conjOpenSubgroup H K 1).toSubgroup := by
    intro h
    change ρ (h : H) w = w
    have he := hw h
    change ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom
      (h : H) : ℂ) • ρ (h : H) w = w at he
    simpa only [relativeModularCharacter_identityCoefficient H hH K hK h h.property,
      one_smul] using he
  unfold compactComparisonValue
  rw [compactSubgroupTest_sectionTest]
  exact heckeAction_normalizedIndicator_of_fixed μH ρ hρ
    (Induction.conjOpenSubgroup H K 1) (compact_identityCoefficientSubgroup H hH K hK) hwρ

/-- Every identity-centered compact double-coset section is an actual elementary
comparison value. -/
theorem compactComparisonFunction_sectionTest (hH : IsClosed (H : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (w : V)
    (hw : w ∈ fixedVectors
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ)
      (Induction.conjOpenSubgroup H K 1).toSubgroup) :
    compactComparisonFunction H hH μH ρ hρ (compactSectionTest H μH K hK) w =
      Induction.compactDoubleCosetSection H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ)
        K hK 1 w hw := by
  ext g
  let σ := Langlands.twist
    (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ
  let T := compactSectionTest H μH K hK
  by_cases hg : ∃ h : H, ∃ k : K, g = (h : G) * (k : G)
  · obtain ⟨h, k, rfl⟩ := hg
    have hvalK : compactComparisonValue H hH μH ρ hρ T w (k : G) = w := by
      have hmul := compactComparisonValue_mul H hH μH ρ hρ T w K
        (compactSectionTest_biInvariant H μH K hK).1 k 1
      simpa only [one_mul] using hmul.trans
        (compactComparisonValue_sectionTest_one H μH ρ hρ hH K hK w hw)
    change compactComparisonValue H hH μH ρ hρ T w ((h : G) * (k : G)) =
      Induction.eval H σ (Induction.compactDoubleCosetSection H σ K hK 1 w hw).val
        ((h : G) * (k : G))
    rw [compactComparisonValue_covariant, hvalK]
    have hs : Induction.eval H σ
        (Induction.compactDoubleCosetSection H σ K hK 1 w hw).val ((h : G) * (k : G)) =
          σ h w := by
      simpa only [mul_one] using
        Induction.compactDoubleCosetSection_apply H σ K hK 1 w hw h k
    exact hs.symm
  · have htest : compactSubgroupTest H hH g T = 0 := by
      ext h
      have hn : g⁻¹ * (h : G) ∉ K := by
        intro hm
        apply hg
        refine ⟨h, ⟨(g⁻¹ * (h : G))⁻¹, K.inv_mem hm⟩, ?_⟩
        simp
      simp [T, compactSubgroupTest_apply, compactSectionTest_apply, hn]
    have hz : compactComparisonValue H hH μH ρ hρ T w g = 0 := by
      unfold compactComparisonValue
      rw [htest, map_zero]
      rfl
    change compactComparisonValue H hH μH ρ hρ T w g =
      Induction.eval H σ (Induction.compactDoubleCosetSection H σ K hK 1 w hw).val g
    rw [hz]
    symm
    by_contra hn
    obtain ⟨k, hk, he⟩ := Induction.compactDoubleCosetSection_support_subset H σ K hK
      1 w hw ⟨g, hn, rfl⟩
    have hp : g * (1 * k)⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    exact hg ⟨⟨g * (1 * k)⁻¹, hp⟩, ⟨k, hk⟩, by simp [mul_assoc]⟩

/-- Ambient left translation becomes the original compact-induced right action. -/
theorem compactComparisonFunction_leftTranslate (hH : IsClosed (H : Set G))
    (g : G) (T : SchwartzBruhat G) (w : V) :
    compactComparisonFunction H hH μH ρ hρ (TestFunction.leftTranslate g T) w =
      Induction.compactInduced H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ)
        g (compactComparisonFunction H hH μH ρ hρ T w) := by
  ext x
  change integratedAction μH ρ hρ
      (compactSubgroupTest H hH x (TestFunction.leftTranslate g T)) w =
    integratedAction μH ρ hρ (compactSubgroupTest H hH (x * g) T) w
  congr 2
  ext h
  simp only [compactSubgroupTest_apply, TestFunction.leftTranslate_apply,
    mul_inv_rev, mul_assoc]

/-- Elementary comparison outputs span the entire original compact induction. -/
theorem compactComparison_span (hH : IsClosed (H : Set G)) :
    Submodule.span ℂ
      {f | ∃ (T : SchwartzBruhat G) (w : V),
        f = compactComparisonFunction H hH μH ρ hρ T w} = ⊤ := by
  let σ := Langlands.twist
    (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ
  have hspan := Induction.compactLocalSectionSpanning G
    (fun O hO h1 => compactOpenSubgroupBasis G O (hO.mem_nhds h1)) H hH V σ
  apply top_le_iff.mp
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro f ⟨g, K, hK, w, hw, rfl⟩
  apply Submodule.subset_span
  refine ⟨TestFunction.leftTranslate g (compactSectionTest H μH K hK), w, ?_⟩
  rw [compactComparisonFunction_leftTranslate, compactComparisonFunction_sectionTest]

/-- Any additive map whose image contains all elementary comparison outputs
is surjective. In particular this applies to the original balanced tensor
lift, without first placing a complex module structure on that quotient. -/
theorem compactComparison_surjective_of_pure_values
    (hH : IsClosed (H : Set G)) {X : Type*} [AddCommGroup X]
    (F : X →+ Induction.CompactFunctions H
      (Langlands.twist
        (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ))
    (hF : ∀ (T : SchwartzBruhat G) (w : V),
      compactComparisonFunction H hH μH ρ hρ T w ∈ F.range) :
    Function.Surjective F := by
  intro f
  have hf : f ∈ Submodule.span ℂ
      {s | ∃ (T : SchwartzBruhat G) (w : V),
        s = compactComparisonFunction H hH μH ρ hρ T w} := by
    rw [compactComparison_span H μH ρ hρ hH]
    trivial
  have hf' : ∀ c : ℂ, c • f ∈ F.range := by
    induction hf using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨T, w, rfl⟩ := hs
      intro c
      have he : compactComparisonFunction H hH μH ρ hρ (c • T) w =
          c • compactComparisonFunction H hH μH ρ hρ T w :=
        congrArg (fun L => L w) (map_smul (compactComparisonBilinear H hH μH ρ hρ) c T)
      rw [← he]
      exact hF (c • T) w
    | zero =>
      intro c
      simpa only [smul_zero] using F.range.zero_mem
    | add x y _ _ hx hy =>
      intro c
      simpa only [smul_add] using F.range.add_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      simpa only [smul_smul] using hx (c * a)
  change f ∈ F.range
  simpa only [one_smul] using hf' 1

end Langlands.Hecke.Homomorphism
