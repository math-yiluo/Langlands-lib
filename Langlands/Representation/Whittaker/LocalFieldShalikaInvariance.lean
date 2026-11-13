import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Whittaker.DistributionInvarianceProof
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-!
# Shalika invariance of Whittaker bi-equivariant distributions over every local field

The published proof of `ShalikaDistributionInvarianceStatement` is carried out for
`PadicField` only through its last specializations: every generic lemma it uses holds
over any field with the relevant topological properties. This module repeats those
specializations over an arbitrary nonarchimedean local field `F` (any characteristic),
with the topological certificates of `Langlands.Group.GL.LocalFieldTopology` in place
of the p-adic ones. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Whittaker.LocalField

open Langlands.GeneralLinear HarmonicAnalysis HarmonicAnalysis.Distribution MeasureTheory

universe uF

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.totallyDisconnectedSpace
  LocalFieldTopology.units_locallyCompactSpace
  LocalFieldTopology.units_totallyDisconnectedSpace
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace
  LocalFieldTopology.upperUnipotent_locallyCompactSpace
  LocalFieldTopology.upperUnipotent_nonarchimedean

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Haar measures on the actual unipotent and Bruhat fiber groups over `F`
(the content of `BruhatHaarMeasureStatement` over every local field). -/
theorem bruhatHaarMeasure (n : ℕ) :
    let U := upperUnipotent (n + 1) F
    letI := borel U
    (∃ μ : Measure U, μ.IsHaarMeasure) ∧
    (∀ (μ : Measure U) [μ.IsHaarMeasure],
      SigmaFinite μ ∧ μ.IsMulRightInvariant ∧
        Measure.map (weylTransposeUnipotent n F) μ = μ) ∧
    ∀ w : Equiv.Perm (Fin (n + 1)),
      let P := permutationUnipotentPlus (n + 1) F w
      letI := borel P
      (∃ ν : Measure P, ν.IsHaarMeasure) ∧
      (∀ (ν : Measure P) [ν.IsHaarMeasure],
        SigmaFinite ν ∧ ν.IsMulRightInvariant) := by
  intro U
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have hUclosed : IsClosed (U : Set (GeneralLinear (n + 1) F)) :=
    UpperUnipotent.isClosed (R := F) (n := n + 1)
  have : LocallyCompactSpace U := hUclosed.locallyCompactSpace
  have : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hUcover : ∀ g : U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ g ∈ K :=
    RankinSelberg.unipotent_exists_compact_open F n
  have hUinv (μ : Measure U) [Measure.IsHaarMeasure μ] : μ.IsMulRightInvariant :=
    isMulRightInvariant_of_compactOpenCover hUcover μ
  refine ⟨⟨Measure.haar, inferInstance⟩, fun μ _ => ⟨inferInstance, hUinv μ, ?_⟩, fun w => ?_⟩
  · have := hUinv μ
    exact map_eq_self_of_antiInvolution (weylTransposeUnipotent n F)
      (fun x y => Subtype.ext (weylTransposeHomeomorph_mul n F x.val y.val))
      (weylTransposeUnipotent_involutive n F) μ
  · intro P
    let : MeasurableSpace P := borel P
    have : BorelSpace P := ⟨rfl⟩
    have hPclosed : IsClosed (P : Set (GeneralLinear (n + 1) F)) :=
      isClosed_permutationUnipotentPlus (n + 1) F w
    have : LocallyCompactSpace P := hPclosed.locallyCompactSpace
    have : SecondCountableTopology P :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have hPcover : ∀ h : P, ∃ L : OpenSubgroup P, IsCompact (L : Set P) ∧ h ∈ L :=
      compactOpenCover_of_le (permutationUnipotentPlus_le_upperUnipotent (n + 1) F w)
        hPclosed hUcover
    exact ⟨⟨Measure.haar, inferInstance⟩, fun ν _ =>
      ⟨inferInstance, isMulRightInvariant_of_compactOpenCover hPcover ν⟩⟩

/-- Shalika's orbital integration onto test functions on the upper Bruhat cell over `F`
(the content of `BruhatOrbitalIntegrationStatement` over every local field). -/
theorem bruhatOrbitalIntegration (n : ℕ) (w : Equiv.Perm (Fin (n + 1))) :
    let U := upperUnipotent (n + 1) F
    let P := permutationUnipotentPlus (n + 1) F w
    let H := Fin (n + 1) → Fˣ
    let M := U × (H × U)
    let C := UpperBruhatCell (n + 1) F w
    letI := borel P
    ∀ (μ : Measure P) [Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant],
      ∃! I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C,
        (∀ (α : SchwartzBruhat M) (m : M),
          I α (upperBruhatTorusMap (n + 1) w m) =
            bruhatFiberAverage (n + 1) F w μ α m) ∧
        Function.Surjective I ∧
        (∀ α : SchwartzBruhat M,
          tsupport (I α : C → ℂ) ⊆
            upperBruhatTorusMap (n + 1) w '' tsupport (α : M → ℂ)) := by
  obtain ⟨-, eT, heT⟩ := upperBruhatCoordinates F (n + 1) w
  obtain ⟨e, he⟩ := upperUnipotentFactorization F (n + 1) w
  obtain ⟨L, hLc, -⟩ := LocalFieldTopology.generalLinear_compactOpen F (n + 1) Set.univ
    Filter.univ_mem
  let K₀ : Set (permutationUnipotentPlus (n + 1) F w) :=
    Subtype.val ⁻¹' (L : Set (GeneralLinear (n + 1) F))
  have hK₀c : IsCompact K₀ :=
    (isClosed_permutationUnipotentPlus (n + 1) F w).isClosedEmbedding_subtypeVal.isCompact_preimage
      hLc
  have hK₀o : IsOpen K₀ := L.isOpen.preimage continuous_subtype_val
  have hK₀ : K₀.Nonempty := ⟨1, L.one_mem⟩
  exact existsUnique_bruhatOrbitalIntegration eT heT e he hK₀c hK₀o hK₀

/-- Character covariance of the product average under Shalika's fiber action over `F`
(the content of `BruhatFiberCharacterCovarianceStatement` over every local field). -/
theorem bruhatFiberCharacterCovariance (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (w : Equiv.Perm (Fin (n + 1))) :
    let U := upperUnipotent (n + 1) F
    let P := permutationUnipotentPlus (n + 1) F w
    let H := Fin (n + 1) → Fˣ
    let M := U × (H × U)
    letI := borel U
    letI : BorelSpace U := ⟨rfl⟩
    ∀ (μ : Measure U) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
      (α : SchwartzBruhat M) (u : P) (d : H),
      SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ
          (Hecke.TestFunction.pullback
            (bruhatFiberActHomeomorph (n + 1) F w u) α) d =
        (compatibilityDefect ψ n w
            (Subgroup.inclusion
              (permutationUnipotentPlus_le_upperUnipotent (n + 1) F w) u) d)⁻¹ *
          SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ α d := by
  intro U P H M
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  intro μ _ _ _ _ α u d
  let g : U := ⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val⁻¹ *
      (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F w)⁻¹,
    permutation_diagonal_conj_inv_mem_upperUnipotent (n + 1) F w d u⟩
  let ι := Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent (n + 1) F w)
  have hmp : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight g) (MeasurableEquiv.mulLeft (ι u)))
      (μ.prod μ) (μ.prod μ) :=
    (measurePreserving_mul_right μ g).prod (measurePreserving_mul_left μ (ι u))
  have hact : ∀ z : U × U,
      bruhatFiberAct (n + 1) F w u (z.1, (d, z.2)) = (z.1 * g, (d, ι u * z.2)) := by
    intro z
    refine Prod.ext (Subtype.ext ?_) rfl
    rw [bruhatFiberAct_fst_val]
    change z.1.val * permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F w)⁻¹ =
      z.1.val * (permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F w)⁻¹)
    simp only [mul_assoc]
  have hu : permutation (n + 1) F w * (ι u).val *
      (permutation (n + 1) F w)⁻¹ ∈ upperUnipotent (n + 1) F :=
    ((mem_permutationUnipotentPlus_iff _ _ _ _).mp u.property).2
  let k : U := ⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * (ι u).val *
      (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
    monomial_conj_mem_upperUnipotent w d hu⟩
  have hdef : compatibilityDefect ψ n w (ι u) d =
      (standardCharacter ψ n k : ℂ) / (standardCharacter ψ n (ι u) : ℂ) :=
    compatibilityDefect_eq_div ψ n w hu d
  have hgk : g * k = 1 := by
    apply Subtype.ext
    change permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation (n + 1) F w)⁻¹ *
      (permutation (n + 1) F w * Iwasawa.diagonalUnits d * u.val *
        (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹) = 1
    group
  have hχgk : (standardCharacter ψ n g : ℂ) * (standardCharacter ψ n k : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hgk, map_one, Units.val_one]
  change ∫ z : U × U, α (bruhatFiberAct (n + 1) F w u (z.1, (d, z.2))) *
        ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ ∂(μ.prod μ) =
      (compatibilityDefect ψ n w (ι u) d)⁻¹ *
        ∫ z : U × U, α (z.1, (d, z.2)) *
          ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ ∂(μ.prod μ)
  rw [← hmp.integral_comp' (fun v : U × U => α (v.1, (d, v.2)) *
      ((standardCharacter ψ n v.1 : ℂ) * (standardCharacter ψ n v.2 : ℂ))⁻¹),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change α (bruhatFiberAct (n + 1) F w u (z.1, (d, z.2))) *
      ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ =
    (compatibilityDefect ψ n w (ι u) d)⁻¹ *
      (α (z.1 * g, (d, ι u * z.2)) *
        ((standardCharacter ψ n (z.1 * g) : ℂ) * (standardCharacter ψ n (ι u * z.2) : ℂ))⁻¹)
  rw [hact z, hdef, map_mul, map_mul, Units.val_mul, Units.val_mul]
  have hk : (standardCharacter ψ n k : ℂ) ≠ 0 := (standardCharacter ψ n k).ne_zero
  have hι : (standardCharacter ψ n (ι u) : ℂ) ≠ 0 := (standardCharacter ψ n (ι u)).ne_zero
  have h₁ : (standardCharacter ψ n z.1 : ℂ) ≠ 0 := (standardCharacter ψ n z.1).ne_zero
  have h₂ : (standardCharacter ψ n z.2 : ℂ) ≠ 0 := (standardCharacter ψ n z.2).ne_zero
  rw [eq_inv_of_mul_eq_one_left hχgk]
  field_simp

open BruhatCompatibleSupport in
/-- Support on the compatible torus from invariance under the fiber action over `F`
(the content of `BruhatCompatibleSupportStatement` over every local field). -/
theorem bruhatCompatibleSupport (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (w : Equiv.Perm (Fin (n + 1))) :
    let U := upperUnipotent (n + 1) F
    let P := permutationUnipotentPlus (n + 1) F w
    let H := Fin (n + 1) → Fˣ
    let M := U × (H × U)
    letI := borel U
    letI : BorelSpace U := ⟨rfl⟩
    ∀ (μ : Measure U) [Measure.IsHaarMeasure μ] [SFinite μ]
      [μ.IsMulRightInvariant] (τ : Distribution H),
      (∀ (u : P) (α : SchwartzBruhat M),
        Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ
            (Hecke.TestFunction.pullback
              (bruhatFiberActHomeomorph (n + 1) F w u) α) =
          Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ α) →
        τ ∈ Distribution.supportedOn (compatibleTorus ψ n w) := by
  intro U P H M
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  intro μ _ _ _ τ hinv
  set χ := standardCharacterContinuous ψ n with hχ
  have hsurj : Function.Surjective (SchwartzBruhat.characterAverage (Y := H) χ μ) :=
    SchwartzBruhat.characterAverageSurjective U H χ μ
  have hlocal : ∀ (u : P) (c : ℂ), c ≠ 1 → ∀ g : SchwartzBruhat H,
      (∀ d, g d ≠ 0 → compatibilityDefect ψ n w
        (Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent (n + 1) F w) u)
          d = c) → τ g = 0 := by
    intro u c hc g hg
    obtain ⟨α, rfl⟩ := hsurj g
    have heq : SchwartzBruhat.characterAverage χ μ
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F w u) α) =
          c⁻¹ • SchwartzBruhat.characterAverage χ μ α := by
      ext d
      rw [bruhatFiberCharacterCovariance F n ψ w μ α u d]
      change _ = c⁻¹ * SchwartzBruhat.characterAverage χ μ α d
      by_cases hd : SchwartzBruhat.characterAverage χ μ α d = 0
      · rw [hd, mul_zero, mul_zero]
      · rw [hg d hd]
    have h := hinv u α
    rw [Distribution.characterAverageDual_apply, Distribution.characterAverageDual_apply,
      heq, map_smul, smul_eq_mul] at h
    have h' : (c⁻¹ - 1) * τ (SchwartzBruhat.characterAverage χ μ α) = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd (inv_eq_one.mp (sub_eq_zero.mp h0)) hc
    · exact h0
  rw [Distribution.mem_supportedOn_iff]
  intro f hf
  apply apply_eq_zero_of_local τ f
  intro d₀ hd₀
  have hnot : d₀ ∉ compatibleTorus ψ n w := fun hmem => hd₀ (hf d₀ hmem)
  rw [mem_compatibleTorus_iff_defect] at hnot
  push Not at hnot
  obtain ⟨v, hv, hne⟩ := hnot
  let u : P := ⟨v.val,
    (mem_permutationUnipotentPlus_iff (n + 1) F w v.val).mpr ⟨v.property, hv⟩⟩
  have hincl : Subgroup.inclusion
      (permutationUnipotentPlus_le_upperUnipotent (n + 1) F w) u = v :=
    Subtype.ext rfl
  have hconj : Continuous fun d : H =>
      (⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * v.val *
          (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
        monomial_conj_mem_upperUnipotent w d hv⟩ : U) := by
    have hs : Continuous fun d : H =>
        permutation (n + 1) F w * Iwasawa.diagonalUnits d :=
      continuous_const.mul (continuous_diagonalUnits (n + 1))
    exact ((hs.mul continuous_const).mul hs.inv).subtype_mk _
  have hχlc : IsLocallyConstant fun x : U => (standardCharacter ψ n x : ℂ) :=
    RankinSelberg.isLocallyConstant_of_continuous_complex_character (standardCharacter ψ n)
      χ.continuous
  have hdef : compatibilityDefect ψ n w v =
      (fun z : ℂ => z / (standardCharacter ψ n v : ℂ)) ∘
        (fun x : U => (standardCharacter ψ n x : ℂ)) ∘
          fun d : H =>
            (⟨permutation (n + 1) F w * Iwasawa.diagonalUnits d * v.val *
                (permutation (n + 1) F w * Iwasawa.diagonalUnits d)⁻¹,
              monomial_conj_mem_upperUnipotent w d hv⟩ : U) :=
    funext fun d => compatibilityDefect_eq_div ψ n w hv d
  have hlc : IsLocallyConstant (compatibilityDefect ψ n w v) := by
    rw [hdef]
    exact (hχlc.comp_continuous hconj).comp _
  refine ⟨{d | compatibilityDefect ψ n w v d = compatibilityDefect ψ n w v d₀},
    hlc.isClopen_fiber _, rfl, fun g hg => ?_⟩
  refine hlocal u _ hne g fun d hd => ?_
  rw [hincl]
  exact hg d hd

open BruhatCellFactorization in
/-- Factorization of a bi-equivariant cell distribution through the character average over
`F` (the content of `BruhatCellFactorizationStatement` over every local field). -/
theorem bruhatCellFactorization (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (w : Equiv.Perm (Fin (n + 1))) :
    let U := upperUnipotent (n + 1) F
    let P := permutationUnipotentPlus (n + 1) F w
    let H := Fin (n + 1) → Fˣ
    let M := U × (H × U)
    let C := UpperBruhatCell (n + 1) F w
    letI := borel U
    letI : BorelSpace U := ⟨rfl⟩
    letI := borel P
    ∀ (μ : Measure U) [Measure.IsHaarMeasure μ] [SFinite μ]
      [μ.IsMulRightInvariant]
      (ν : Measure P) [Measure.IsHaarMeasure ν] [ν.IsMulRightInvariant]
      (I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C),
      (∀ (α : SchwartzBruhat M) (m : M),
        I α (upperBruhatTorusMap (n + 1) w m) =
          bruhatFiberAverage (n + 1) F w ν α m) →
      ∀ D : Distribution C,
        IsBiEquivariantBruhatCellDistribution n F w ψ D →
        ∃! τ : Distribution H,
          τ ∈ Distribution.supportedOn (compatibleTorus ψ n w) ∧
            Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ =
              D.comp I := by
  intro U P H M C
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  let := borel P
  intro μ _ _ _ ν _ _ I hI D hD
  have hπ := torusMap_surjective (K := F) w
  obtain ⟨τ, hτ, hunique⟩ :=
    Distribution.characterAverageFactorization U H (standardCharacterContinuous ψ n) μ
      (D.comp I) (by
        intro a b α
        change D (I (Hecke.TestFunction.pullback _ α)) = _
        rw [orbitalIntegral_pullback_productTranslate ν I hI hπ]
        exact hD a b (I α))
  refine ⟨τ, ⟨?_, hτ⟩, ?_⟩
  · apply bruhatCompatibleSupport F n ψ w μ τ
    intro u α
    rw [hτ]
    change D (I (Hecke.TestFunction.pullback _ α)) = D (I α)
    rw [orbitalIntegral_pullback_fiberAct ν I hI hπ
      (inferInstance : ν.IsMulLeftInvariant)]
  · intro τ' hτ'
    exact hunique τ' hτ'.2

/-- Vanishing on character-incompatible Bruhat cells over `F` (the content of
`BruhatCellVanishingStatement` over every local field). -/
theorem bruhatCellVanishing (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (w : Equiv.Perm (Fin (n + 1))) (hempty : ¬ (compatibleTorus ψ n w).Nonempty)
    (D : Distribution (UpperBruhatCell (n + 1) F w))
    (hD : IsBiEquivariantBruhatCellDistribution n F w ψ D) : D = 0 := by
  let U := upperUnipotent (n + 1) F
  let P := permutationUnipotentPlus (n + 1) F w
  let H := Fin (n + 1) → Fˣ
  let M := U × (H × U)
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  let := borel P
  obtain ⟨μ, hμ⟩ := (bruhatHaarMeasure F n).1
  have := hμ
  obtain ⟨hσ, hr, -⟩ := (bruhatHaarMeasure F n).2.1 μ
  have := hσ
  have := hr
  obtain ⟨ν, hν⟩ := ((bruhatHaarMeasure F n).2.2 w).1
  have := hν
  have := (((bruhatHaarMeasure F n).2.2 w).2 ν).2
  obtain ⟨I, ⟨hI, hsurj, -⟩, -⟩ := bruhatOrbitalIntegration F n w ν
  obtain ⟨τ, ⟨hsupp, hτ⟩, -⟩ := bruhatCellFactorization F n ψ w μ ν I hI D hD
  have hzero : τ = 0 := by
    ext f
    apply (Distribution.mem_supportedOn_iff _ _).mp hsupp f
    intro d hd
    exact (hempty ⟨d, hd⟩).elim
  have hcomp : D.comp I = 0 := by
    rw [← hτ, hzero, map_zero]
  ext f
  obtain ⟨α, rfl⟩ := hsurj f
  exact congrArg (fun E : Distribution M => E α) hcomp

open BruhatCellInvariance in
/-- Cell stability and transpose invariance on Bruhat cells with nonempty compatible torus
over `F` (the content of `BruhatCellInvarianceStatement` over every local field). -/
theorem bruhatCellInvariance (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (w : Equiv.Perm (Fin (n + 1))) (hnon : (compatibleTorus ψ n w).Nonempty) :
    ∃ hτ : Set.MapsTo (weylTransposeHomeomorph n F)
      (upperBruhatCell (n + 1) F w) (upperBruhatCell (n + 1) F w),
      ∀ D : Distribution (UpperBruhatCell (n + 1) F w),
        IsBiEquivariantBruhatCellDistribution n F w ψ D →
          IsWeylTransposeInvariantBruhatCellDistribution n F w hτ D := by
  have hfixed (d : Fin (n + 1) → Fˣ) (hd : d ∈ compatibleTorus ψ n w) :
      weylTransposeHomeomorph n F (permutation (n + 1) F w * Iwasawa.diagonalUnits d) =
        permutation (n + 1) F w * Iwasawa.diagonalUnits d :=
    weylTransposeHomeomorph_monomial_eq_of_compatible ψ w d hd
  obtain ⟨d₀, hd₀⟩ := hnon
  let hτ := cell_stable_of_fixed_monomial w d₀ (hfixed d₀ hd₀)
  refine ⟨hτ, ?_⟩
  intro D hD
  let U := upperUnipotent (n + 1) F
  let P := permutationUnipotentPlus (n + 1) F w
  let H := Fin (n + 1) → Fˣ
  let M := U × (H × U)
  let C := UpperBruhatCell (n + 1) F w
  let := borel U
  have : BorelSpace U := ⟨rfl⟩
  let := borel P
  have : BorelSpace P := ⟨rfl⟩
  have : LocallyCompactSpace P :=
    (isClosed_permutationUnipotentPlus (n + 1) F w).locallyCompactSpace
  have : SecondCountableTopology P := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨μ, hμ⟩ := (bruhatHaarMeasure F n).1
  have := hμ
  obtain ⟨hσ, hr, htranspose⟩ := (bruhatHaarMeasure F n).2.1 μ
  have := hσ
  have := hr
  obtain ⟨ν, hν⟩ := ((bruhatHaarMeasure F n).2.2 w).1
  have := hν
  have := (((bruhatHaarMeasure F n).2.2 w).2 ν).2
  obtain ⟨I, ⟨hI, hsurj, -⟩, -⟩ := bruhatOrbitalIntegration F n w ν
  obtain ⟨τ, ⟨hsupp, hτfac⟩, -⟩ := bruhatCellFactorization F n ψ w μ ν I hI D hD
  obtain ⟨-, eT, heT⟩ := upperBruhatCoordinates F (n + 1) w
  obtain ⟨e, he⟩ := upperUnipotentFactorization F (n + 1) w
  obtain ⟨L, hLc, -⟩ := LocalFieldTopology.generalLinear_compactOpen F (n + 1) Set.univ
    Filter.univ_mem
  let K₀ : Set P := Subtype.val ⁻¹' (L : Set (GeneralLinear (n + 1) F))
  have hK₀c : IsCompact K₀ :=
    (isClosed_permutationUnipotentPlus (n + 1) F w).isClosedEmbedding_subtypeVal.isCompact_preimage
      hLc
  have hK₀o : IsOpen K₀ := L.isOpen.preimage continuous_subtype_val
  have hK₀ : K₀.Nonempty := ⟨1, L.one_mem⟩
  have hDsupp : D ∈ Distribution.supportedOn
      {c | (eT.symm c).2.1 ∈ compatibleTorus ψ n w} :=
    supportedOn_middle_of_factorization heT he hK₀c hK₀o hK₀
      (standardCharacterContinuous ψ n) μ ν I hI D τ _ hsupp hτfac
  have hfac_eval (β : SchwartzBruhat M) :
      D (I β) = τ (SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ β) :=
    (congrArg (fun E => E β) hτfac).symm
  apply (isWeylTransposeInvariantBruhatCellDistribution_iff n F w hτ D).mpr
  intro f
  obtain ⟨α, rfl⟩ := hsurj f
  have hDexchange :
      D (I (Hecke.TestFunction.pullback (productTranspose n F) α)) = D (I α) := by
    rw [hfac_eval, hfac_eval, characterAverage_productTranspose ψ μ htranspose]
  have hdiff : D
      (Hecke.TestFunction.pullback (bruhatCellWeylTranspose n F w hτ) (I α) -
        I (Hecke.TestFunction.pullback (productTranspose n F) α)) = 0 := by
    apply (Distribution.mem_supportedOn_iff _ _).mp hDsupp
    intro c hc
    let m : M := cellSection eT c
    have hm : upperBruhatTorusMap (n + 1) w m = c :=
      upperBruhatTorusMap_cellSection heT c
    have hmd : m.2.1 ∈ compatibleTorus ψ n w := hc
    have hπσ : upperBruhatTorusMap (n + 1) w (productTranspose n F m) =
        bruhatCellWeylTranspose n F w hτ c := by
      apply Subtype.ext
      rw [upperBruhatTorusMap_productTranspose w m (hfixed _ hmd)]
      exact congrArg (fun z : C => weylTransposeHomeomorph n F z.val) hm
    have hpoint :
        I (Hecke.TestFunction.pullback (productTranspose n F) α) c =
          I α (bruhatCellWeylTranspose n F w hτ c) := by
      calc
        _ = I (Hecke.TestFunction.pullback (productTranspose n F) α)
            (upperBruhatTorusMap (n + 1) w m) := by rw [hm]
        _ = bruhatFiberAverage (n + 1) F w ν
            (Hecke.TestFunction.pullback (productTranspose n F) α) m := hI _ _
        _ = bruhatFiberAverage (n + 1) F w ν α (productTranspose n F m) :=
          bruhatFiberAverage_productTranspose w ν α m (hfixed _ hmd)
        _ = I α (upperBruhatTorusMap (n + 1) w (productTranspose n F m)) :=
          (hI _ _).symm
        _ = _ := congrArg (I α) hπσ
    change I α (bruhatCellWeylTranspose n F w hτ c) -
      I (Hecke.TestFunction.pullback (productTranspose n F) α) c = 0
    rw [hpoint, sub_self]
  rw [map_sub] at hdiff
  exact (sub_eq_zero.mp hdiff).trans hDexchange

section Difference

variable {F}

private theorem pullback_transpose_biTranslate (n : ℕ)
    (u₁ u₂ : upperUnipotent (n + 1) F)
    (f : SchwartzBruhat (GeneralLinear (n + 1) F)) :
    Hecke.TestFunction.pullback (weylTransposeHomeomorph n F)
        (Hecke.TestFunction.pullback
          ((Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)) f) =
      Hecke.TestFunction.pullback
        ((Homeomorph.mulLeft (weylTransposeUnipotent n F u₂).val).trans
          (Homeomorph.mulRight (weylTransposeUnipotent n F u₁).val))
        (Hecke.TestFunction.pullback (weylTransposeHomeomorph n F) f) := by
  ext g
  change f (u₁.val * weylTransposeHomeomorph n F g * u₂.val) =
    f (weylTransposeHomeomorph n F
      ((weylTransposeUnipotent n F u₂).val * g *
        (weylTransposeUnipotent n F u₁).val))
  simp only [weylTransposeHomeomorph_mul, weylTransposeUnipotent_val,
    weylTransposeHomeomorph_involutive, mul_assoc]

private theorem biEquivariant_difference (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (D : Distribution (GeneralLinear (n + 1) F))
    (hD : IsBiEquivariantDistribution ψ n D) :
    IsBiEquivariantDistribution ψ n
      (D - pushforward (weylTransposeHomeomorph n F) D) := by
  have hpush : IsBiEquivariantDistribution ψ n
      (pushforward (weylTransposeHomeomorph n F) D) := by
    apply (isBiEquivariantDistribution_iff n F ψ _).mpr
    intro u₁ u₂ f
    change D (Hecke.TestFunction.pullback (weylTransposeHomeomorph n F)
        (Hecke.TestFunction.pullback
          ((Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)) f)) =
      ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) *
        D (Hecke.TestFunction.pullback (weylTransposeHomeomorph n F) f)
    rw [pullback_transpose_biTranslate]
    have h := (isBiEquivariantDistribution_iff n F ψ D).mp hD
      (weylTransposeUnipotent n F u₂) (weylTransposeUnipotent n F u₁)
      (Hecke.TestFunction.pullback (weylTransposeHomeomorph n F) f)
    simpa only [standardCharacter_weylTranspose, mul_comm] using h
  intro u₁ u₂ f
  change D _ - pushforward (weylTransposeHomeomorph n F) D _ =
    _ * (D f - pushforward (weylTransposeHomeomorph n F) D f)
  rw [hD, hpush, mul_sub]

end Difference

/-- Every Whittaker bi-equivariant algebraic distribution on `GL_(n+1)(F)` is invariant
under the Weyl-conjugated transpose, over every nonarchimedean local field `F` (the
content of `ShalikaDistributionInvarianceStatement` over every local field). -/
theorem shalikaDistributionInvariance (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (D : Distribution (GeneralLinear (n + 1) F))
    (hD : IsBiEquivariantDistribution ψ n D) :
    IsWeylTransposeInvariant n F D := by
  classical
  let E := D - pushforward (weylTransposeHomeomorph n F) D
  have hEbi : IsBiEquivariantDistribution ψ n E := biEquivariant_difference n ψ D hD
  have hEanti : pushforward (weylTransposeHomeomorph n F) E = -E := by
    simp only [E, map_sub, pushforward_weylTranspose_involutive, neg_sub]
  have hEzero : E = 0 := by
    apply bruhatFiltrationVanishing (n + 1) F E
    intro w hw
    apply bruhatCellRestrictionVanishing n F w ψ ⟨E, hw⟩ hEbi hEanti
    by_cases hnon : (compatibleTorus ψ n w).Nonempty
    · exact Or.inr (bruhatCellInvariance F n ψ w hnon)
    · exact Or.inl (bruhatCellVanishing F n ψ w hnon)
  exact (sub_eq_zero.mp hEzero).symm

end Langlands.Whittaker.LocalField
