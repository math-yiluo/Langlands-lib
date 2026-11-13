import Langlands.HarmonicAnalysis.Distribution.RenardHeckeCompactHaar
import Langlands.HarmonicAnalysis.Distribution.RenardHeckeStatements
import Langlands.Representation.Hecke.LocalUnitsProof
import Langlands.Representation.Hecke.DoubleCosetSandwich

/-! # Renard II.3.12: proof of the distribution realization of Hecke corners -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardHecke

universe uG

open Hecke.HeckeAlgebra in
/-- Conjunct 1: the density realization is faithful with the test-density range. -/
theorem densityRealization : DensityRealizationStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  refine ⟨fun a b h => testDensity_injective μ h, ?_⟩
  ext D
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩

/-- Conjunct 2: the normalized indicator realizes `e_K`. -/
theorem normalizedIndicatorRealization : NormalizedIndicatorStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ K hK
  exact heckeDistribution_normalizedIndicator μ K hK

/-- Conjunct 3: finite families of Hecke distributions have compact-open local units. -/
theorem localUnits : LocalUnitsStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ s U hs
  classical
  let pre : compactlySupported (X := G) → Hecke.HeckeAlgebra μ := fun T =>
    if h : (T : Distribution G) ∈ heckeDistributionSpace μ then h.choose else 0
  have hpre : ∀ T ∈ s, compactTestDensity μ (pre T) = T := by
    intro T hT
    apply Subtype.ext
    have h := hs T hT
    simp only [pre, h, ↓reduceDIte]
    exact h.choose_spec
  obtain ⟨K, hK, hKU, -, hunits⟩ :=
    Hecke.HeckeAlgebra.finiteFamilyLocalUnits G μ (s.image pre) U
  refine ⟨K, hK, hKU, fun T hT => ?_⟩
  have hu := hunits (pre T) (Finset.mem_image_of_mem pre hT)
  have hT' := hpre T hT
  have he := compactTestDensity_normalizedIndicator μ K hK
  constructor
  · calc convolution (compactSubgroupHaar K.toSubgroup hK) T
        = convolution (compactTestDensity μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK))
            (compactTestDensity μ (pre T)) := by rw [he, hT']
      _ = compactTestDensity μ (Hecke.TestFunction.convolution μ
            (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) (pre T)) :=
          convolution_compactTestDensity μ _ _
      _ = T := (congrArg (compactTestDensity μ) hu.1).trans hT'
  · calc convolution T (compactSubgroupHaar K.toSubgroup hK)
        = convolution (compactTestDensity μ (pre T))
            (compactTestDensity μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) := by
          rw [he, hT']
      _ = compactTestDensity μ (Hecke.TestFunction.convolution μ
            (pre T) (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) :=
          convolution_compactTestDensity μ _ _
      _ = T := (congrArg (compactTestDensity μ) hu.2).trans hT'

section Bridge

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The product of two compact-open idempotents is the density of the Hecke product. -/
theorem convolution_compactSubgroupHaar_compactSubgroupHaar (K L : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G)) :
    convolution (compactSubgroupHaar K.toSubgroup hK) (compactSubgroupHaar L.toSubgroup hL) =
      compactTestDensity μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK *
        Hecke.HeckeAlgebra.normalizedIndicator μ L hL) := by
  rw [← compactTestDensity_normalizedIndicator μ K hK,
    ← compactTestDensity_normalizedIndicator μ L hL]
  exact convolution_compactTestDensity μ _ _

end Bridge

/-- Conjunct 4: `e_K e_L = e_L e_K = e_K` exactly when `L ≤ K`. -/
theorem idempotentOrder : IdempotentOrderStatement.{uG} := by
  intro G _ _ _ _ _ _ K L hK hL
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure G, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have hKe := compactTestDensity_normalizedIndicator μ K hK
  constructor
  · rintro ⟨h1, -⟩
    rw [convolution_compactSubgroupHaar_compactSubgroupHaar μ, ← hKe] at h1
    have h2 : Hecke.TestFunction.convolution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
        (Hecke.HeckeAlgebra.normalizedIndicator μ L hL) =
        Hecke.HeckeAlgebra.normalizedIndicator μ K hK :=
      testDensity_injective μ (congrArg Subtype.val h1)
    intro l hl
    have h3 := Hecke.TestFunction.convolution_rightInvariant μ
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
      (Hecke.HeckeAlgebra.normalizedIndicator_mem_biInvariant μ L hL).2 ⟨l, hl⟩ 1
    rw [h2] at h3
    by_contra hlK
    have h4 : Hecke.HeckeAlgebra.normalizedIndicator μ K hK ((1 : G) * l) =
        Hecke.HeckeAlgebra.normalizedIndicator μ K hK 1 := h3
    simp [Hecke.HeckeAlgebra.normalizedIndicator_apply, hlK] at h4
    exact Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK h4.symm
  · intro hLK
    rw [convolution_compactSubgroupHaar_compactSubgroupHaar μ,
      convolution_compactSubgroupHaar_compactSubgroupHaar μ,
      Hecke.HeckeAlgebra.normalizedIndicator_mul_of_ge μ K hK L hL hLK,
      Hecke.HeckeAlgebra.normalizedIndicator_mul_of_le μ K hK L hL hLK]
    exact ⟨hKe, hKe⟩

section Inversion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Inversion of a distribution is supported in the inverse of the support. -/
theorem inversionDistributions_mem_supportedOn (D : Distribution G) :
    GroupAction.inversionDistributions D ∈ supportedOn (support D)⁻¹ := by
  intro f hf
  rw [GroupAction.inversionDistributions_apply]
  apply mem_supportedOn_support D
  intro x hx
  rw [GroupAction.inversionTests_apply]
  exact hf x⁻¹ (Set.inv_mem_inv.mpr hx)

theorem support_inversionDistributions_subset (D : Distribution G) :
    support (GroupAction.inversionDistributions D) ⊆ (support D)⁻¹ :=
  support_subset_of_mem_supportedOn (isClosed_support D).inv
    (inversionDistributions_mem_supportedOn D)

/-- The inversion of a compactly supported distribution, with its compact support. -/
def compactInversion (T : compactlySupported (X := G)) : compactlySupported (X := G) :=
  ⟨GroupAction.inversionDistributions (T : Distribution G),
    T.property.inv.of_isClosed_subset (isClosed_support _)
      (support_inversionDistributions_subset _)⟩

/-- Precomposition of a locally constant function with inversion. -/
def invFunction (φ : LocallyConstant G ℂ) : LocallyConstant G ℂ :=
  ⟨fun x => φ x⁻¹, φ.isLocallyConstant.comp_continuous continuous_inv⟩

/-- Extended evaluation of the inverted distribution is evaluation on `φ ∘ inv`. -/
theorem compactSupportPairing_compactInversion (T : compactlySupported (X := G))
    (φ : LocallyConstant G ℂ) :
    compactSupportPairing (compactInversion T) φ =
      compactSupportPairing T (invFunction φ) := by
  obtain ⟨ψ, hψ⟩ := exists_testFunction_agrees_on_compact T.property (invFunction φ)
  rw [compactSupportPairing_eq_of_agrees T _ ψ hψ,
    compactSupportPairing_eq_of_agrees (compactInversion T) φ (GroupAction.inversionTests ψ)]
  · change (T : Distribution G) (GroupAction.inversionTests (GroupAction.inversionTests ψ)) = _
    rw [GroupAction.inversionTests_inversionTests]
  · intro y hy
    have hy' : y⁻¹ ∈ support (T : Distribution G) :=
      Set.mem_inv.mp (support_inversionDistributions_subset (T : Distribution G) hy)
    rw [GroupAction.inversionTests_apply, hψ _ hy']
    change φ y⁻¹⁻¹ = φ y
    rw [inv_inv]

/-- Inversion reverses compact convolution. -/
theorem inversionDistributions_convolution (T S : compactlySupported (X := G)) :
    GroupAction.inversionDistributions (convolution T S : Distribution G) =
      (convolution (compactInversion S) (compactInversion T) : Distribution G) := by
  ext f
  rw [GroupAction.inversionDistributions_apply, convolution_eq_pairing, convolution_eq_pairing,
    compactPairing_swap T S, compactSupportPairing_compactInversion S]
  refine congrArg (compactSupportPairing S) ?_
  ext y
  change compactSupportPairing T _ = compactSupportPairing (compactInversion T) _
  rw [compactSupportPairing_compactInversion T]
  refine congrArg (compactSupportPairing T) ?_
  ext x
  change f (x * y)⁻¹ = f (y⁻¹ * x⁻¹)
  rw [mul_inv_rev]

end Inversion

/-- Conjunct 5: inversion reverses convolution and fixes `e_K`. -/
theorem inversion : InversionStatement.{uG} := by
  intro G _ _ _ _ _ _
  exact ⟨fun T S => ⟨compactInversion T, compactInversion S, rfl, rfl,
    inversionDistributions_convolution T S⟩,
    fun K hK => inversionDistributions_compactSubgroupHaar K.toSubgroup hK⟩

section Corner

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

theorem convolution_compactSubgroupHaar_compactTestDensity (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : Hecke.HeckeAlgebra μ) :
    convolution (compactSubgroupHaar K.toSubgroup hK) (compactTestDensity μ f) =
      compactTestDensity μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK * f) := by
  rw [← compactTestDensity_normalizedIndicator μ K hK]
  exact convolution_compactTestDensity μ _ _

theorem convolution_compactTestDensity_compactSubgroupHaar (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : Hecke.HeckeAlgebra μ) :
    convolution (compactTestDensity μ f) (compactSubgroupHaar K.toSubgroup hK) =
      compactTestDensity μ (f * Hecke.HeckeAlgebra.normalizedIndicator μ K hK) := by
  rw [← compactTestDensity_normalizedIndicator μ K hK]
  exact convolution_compactTestDensity μ _ _

/-- Densities of corner elements are compact and bi-`K`-invariant. -/
theorem heckeDistribution_corner_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (h : Hecke.HeckeAlgebra.Corner μ K hK) :
    heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK h) ∈
      GroupFunctionSpaces.compactDistributionsBoth K.toSubgroup := by
  set f := Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK h with hf
  have hl : convolution (compactSubgroupHaar K.toSubgroup hK) (compactTestDensity μ f) =
      compactTestDensity μ f := by
    rw [convolution_compactSubgroupHaar_compactTestDensity,
      Hecke.HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant μ K hK f
        (fun k x => Hecke.HeckeAlgebra.Corner.leftInvariant μ K hK h k x)]
  have hr : convolution (compactTestDensity μ f) (compactSubgroupHaar K.toSubgroup hK) =
      compactTestDensity μ f := by
    rw [convolution_compactTestDensity_compactSubgroupHaar,
      Hecke.HeckeAlgebra.mul_normalizedIndicator_of_rightInvariant μ K hK f
        (fun k x => Hecke.HeckeAlgebra.Corner.rightInvariant μ K hK h k x)]
  refine Submodule.mem_inf.mpr ⟨(compactTestDensity μ f).property,
    Submodule.mem_inf.mpr ⟨(GroupFunctionSpaces.mem_fixed_iff _ _ _).mpr fun k => ?_,
      (GroupFunctionSpaces.mem_fixed_iff _ _ _).mpr fun k => ?_⟩⟩
  · have := leftDistributions_convolution (compactSubgroupHaar K.toSubgroup hK)
      (compactTestDensity μ f) k (leftDistributions_compactSubgroupHaar K.toSubgroup hK k.property)
    rw [hl] at this
    exact this
  · have := rightDistributions_convolution (compactTestDensity μ f)
      (compactSubgroupHaar K.toSubgroup hK) k
      (rightDistributions_compactSubgroupHaar K.toSubgroup hK k.property)
    rw [hr] at this
    exact this

end Corner

/-- Conjunct 6: the corner realizes the compact bi-`K`-invariant distributions. -/
theorem corner : CornerStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ K hK
  refine ⟨?_, heckeDistribution_normalizedIndicator μ K hK⟩
  ext D
  constructor
  · rintro ⟨h, rfl⟩
    exact heckeDistribution_corner_mem μ K hK h
  · intro hD
    obtain ⟨hc, hboth⟩ := Submodule.mem_inf.mp hD
    obtain ⟨hl, hr⟩ := Submodule.mem_inf.mp hboth
    let Dc : compactlySupported (X := G) := ⟨D, hc⟩
    have hDl : convolution (compactSubgroupHaar K.toSubgroup hK) Dc = Dc :=
      convolution_compactSubgroupHaar_left K.toSubgroup hK Dc
        (fun k hk => (GroupFunctionSpaces.mem_fixed_iff _ _ _).mp hl ⟨k, hk⟩)
    have hDr : convolution Dc (compactSubgroupHaar K.toSubgroup hK) = Dc :=
      convolution_compactSubgroupHaar_right K.toSubgroup hK Dc
        (fun k hk => (GroupFunctionSpaces.mem_fixed_iff _ _ _).mp hr ⟨k, hk⟩)
    let h0 : Hecke.HeckeAlgebra μ :=
      leftTestFunction Dc (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
    have h0D : compactTestDensity μ h0 = Dc := by
      apply Subtype.ext
      have := convolution_testDensity_left μ Dc (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
      rw [compactTestDensity_normalizedIndicator μ K hK, hDr] at this
      exact this.symm
    refine ⟨Hecke.HeckeAlgebra.Corner.project μ K hK h0, ?_⟩
    change (compactTestDensity μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK * h0 *
      Hecke.HeckeAlgebra.normalizedIndicator μ K hK) : Distribution G) = D
    rw [← convolution_compactTestDensity_compactSubgroupHaar,
      ← convolution_compactSubgroupHaar_compactTestDensity, h0D, hDl, hDr]

section DoubleCoset

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- The normalized indicator has total mass one. -/
theorem integral_normalizedIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    ∫ x, Hecke.HeckeAlgebra.normalizedIndicator μ K hK x ∂μ = 1 := by
  simp only [Hecke.HeckeAlgebra.normalizedIndicator_apply]
  rw [integral_const_mul, integral_indicator_const _ K.isOpen.measurableSet, Complex.real_smul,
    mul_one]
  exact inv_mul_cancel₀ (Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK)

/-- The double-coset sandwich `e_K * δ_g * e_K` is the density of `e * L_g e`. -/
theorem sandwich_compactDirac (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    convolution (convolution (compactSubgroupHaar K.toSubgroup hK) (compactDirac g))
        (compactSubgroupHaar K.toSubgroup hK) =
      compactTestDensity μ (Hecke.TestFunction.convolution μ
        (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
        (GroupAction.leftTests g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK))) := by
  rw [convolution_associative, ← compactTestDensity_normalizedIndicator μ K hK,
    convolution_compactDirac_compactTestDensity μ g
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)]
  exact convolution_compactTestDensity μ _ _

omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- `e * L_g e` is the mass-one indicator of the double coset `KgK`. -/
theorem convolution_normalizedIndicator_leftTests (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) :
    Hecke.TestFunction.convolution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
        (GroupAction.leftTests g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) =
      (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK
        (Hecke.HeckeAlgebra.Corner.massIndicator K hK μ g) : SchwartzBruhat G) := by
  have he := Hecke.HeckeAlgebra.normalizedIndicator_mem_biInvariant μ K hK
  have hLr : ∀ l : K.toSubgroup, ∀ x,
      GroupAction.leftTests g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) (x * (l : G)) =
        GroupAction.leftTests g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) x := by
    intro l x
    change Hecke.HeckeAlgebra.normalizedIndicator μ K hK (g⁻¹ * (x * l)) =
      Hecke.HeckeAlgebra.normalizedIndicator μ K hK (g⁻¹ * x)
    rw [← mul_assoc]
    exact he.2 l (g⁻¹ * x)
  have hmem := Hecke.TestFunction.convolution_mem_biInvariant_of_left_right μ he.1 hLr
  let F : Hecke.HeckeAlgebra.Corner μ K hK :=
    ⟨Hecke.TestFunction.convolution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
      (GroupAction.leftTests g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)), hmem⟩
  suffices hF : F = Hecke.HeckeAlgebra.Corner.massIndicator K hK μ g by
    exact congrArg (fun c => (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK c :
      SchwartzBruhat G)) hF
  have hzero : ∀ x, x ∉ Hecke.TestFunction.doubleCosetSet K g → F x = 0 := by
    intro x hx
    change ∫ y, Hecke.HeckeAlgebra.normalizedIndicator μ K hK y *
      Hecke.HeckeAlgebra.normalizedIndicator μ K hK (g⁻¹ * (y⁻¹ * x)) ∂μ = 0
    have h0 : (fun y => Hecke.HeckeAlgebra.normalizedIndicator μ K hK y *
        Hecke.HeckeAlgebra.normalizedIndicator μ K hK (g⁻¹ * (y⁻¹ * x))) = fun _ => 0 := by
      funext y
      by_cases hy : y ∈ K
      · have hy2 : g⁻¹ * (y⁻¹ * x) ∉ K := fun h2 =>
          hx ((Hecke.TestFunction.mem_doubleCosetSet K g x).2
            ⟨y, hy, _, h2, by simp [mul_assoc]⟩)
        simp [Hecke.HeckeAlgebra.normalizedIndicator_apply, hy2]
      · simp [Hecke.HeckeAlgebra.normalizedIndicator_apply, hy]
    rw [h0, integral_zero]
  have hconst : ∀ x, F x =
      F g * (Hecke.TestFunction.doubleCosetSet K g).indicator (fun _ => (1 : ℂ)) x := by
    intro x
    by_cases hx : x ∈ Hecke.TestFunction.doubleCosetSet K g
    · rw [Set.indicator_of_mem hx, mul_one]
      exact Hecke.HeckeAlgebra.Corner.apply_eq_of_mem_doubleCosetSet K hK μ F hx
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact hzero x hx
  have hint : ∫ x, F x ∂μ = 1 := by
    have h1 := Hecke.HeckeAlgebra.integral_mul μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
      (GroupAction.leftTests g (Hecke.HeckeAlgebra.normalizedIndicator μ K hK))
    have h2 : ∫ x, GroupAction.leftTests g
        (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) x ∂μ = 1 :=
      (integral_mul_left_eq_self
        (fun x => Hecke.HeckeAlgebra.normalizedIndicator μ K hK x) g⁻¹).trans
        (integral_normalizedIndicator μ K hK)
    rw [integral_normalizedIndicator μ K hK, one_mul] at h1
    exact h1.trans h2
  have hFg : F g * (μ.real (Hecke.TestFunction.doubleCosetSet K g) : ℂ) = 1 := by
    rw [← hint]
    calc F g * (μ.real (Hecke.TestFunction.doubleCosetSet K g) : ℂ)
        = ∫ x, F g * (Hecke.TestFunction.doubleCosetSet K g).indicator
            (fun _ => (1 : ℂ)) x ∂μ := by
          rw [integral_const_mul, integral_indicator_const _
            (Hecke.TestFunction.isOpen_doubleCosetSet K g).measurableSet, Complex.real_smul,
            mul_one]
      _ = ∫ x, F x ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun x => (hconst x).symm)
  apply Hecke.HeckeAlgebra.Corner.ext' K hK μ
  intro x
  rw [hconst x, Hecke.HeckeAlgebra.Corner.massIndicator_apply]
  congr 1
  exact eq_inv_of_mul_eq_one_left hFg

/-- The mass-one double-coset element realizes `e_K * δ_g * e_K`. -/
theorem heckeDistribution_massIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) :
    heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK
        (Hecke.HeckeAlgebra.Corner.massIndicator K hK μ g)) =
      (convolution (convolution (compactSubgroupHaar K.toSubgroup hK) (compactDirac g))
        (compactSubgroupHaar K.toSubgroup hK) : Distribution G) := by
  rw [sandwich_compactDirac μ K hK g, convolution_normalizedIndicator_leftTests μ K hK g]
  rfl

end DoubleCoset

/-- Conjunct 7: double-coset elements and the double-coset basis. -/
theorem doubleCosetBasis : DoubleCosetBasisStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ K hK
  refine ⟨fun g => heckeDistribution_massIndicator μ K hK g, ?_⟩
  intro ι r hr
  classical
  let Φ : Hecke.HeckeAlgebra.Corner μ K hK →ₗ[ℂ]
      GroupFunctionSpaces.compactDistributionsBoth K.toSubgroup :=
    { toFun := fun h => ⟨heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK h),
        heckeDistribution_corner_mem μ K hK h⟩
      map_add' := fun a b => Subtype.ext (by
        change heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (a + b)) =
          heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK a) +
            heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK b)
        rw [map_add, map_add])
      map_smul' := fun c a => Subtype.ext (by
        change heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (c • a)) =
          c • heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK a)
        rw [map_smul, map_smul]) }
  have hinj : Function.Injective Φ := by
    intro a b hab
    apply Hecke.HeckeAlgebra.Corner.toHeckeAlgebra_injective μ K hK
    have h1 : testDensity μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK a) =
        testDensity μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK b) :=
      congrArg Subtype.val hab
    exact testDensity_injective μ h1
  have hsurj : Function.Surjective Φ := by
    rintro ⟨D, hD⟩
    obtain ⟨h, hh⟩ : D ∈ Set.range (fun h : Hecke.HeckeAlgebra.Corner μ K hK =>
        heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK h)) := by
      rw [(corner G μ K hK).1]
      exact hD
    exact ⟨h, Subtype.ext hh⟩
  let ev : G → (Hecke.HeckeAlgebra.Corner μ K hK →ₗ[ℂ] ℂ) := fun x =>
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hli : LinearIndependent ℂ
      (fun i => Hecke.HeckeAlgebra.Corner.massIndicator K hK μ (r i)) := by
    rw [linearIndependent_iff']
    intro s c hs j hj
    have h := congrArg (ev (r j)) hs
    rw [map_sum, map_zero, Finset.sum_eq_single j] at h
    · change c j * Hecke.HeckeAlgebra.Corner.massIndicator K hK μ (r j) (r j) = 0 at h
      rw [Hecke.HeckeAlgebra.Corner.massIndicator_apply,
        Set.indicator_of_mem (Hecke.TestFunction.mem_doubleCosetSet_self K (r j)),
        mul_one] at h
      exact (mul_eq_zero.mp h).resolve_right
        (inv_ne_zero (Hecke.HeckeAlgebra.Corner.doubleCosetSet_complex_mass_ne_zero K hK μ (r j)))
    · intro i _ hij
      change c i * Hecke.HeckeAlgebra.Corner.massIndicator K hK μ (r i) (r j) = 0
      rw [Hecke.HeckeAlgebra.Corner.massIndicator_apply, Set.indicator_of_notMem, mul_zero,
        mul_zero]
      intro hmem
      apply hij
      obtain ⟨k, -, hk⟩ := hr (r j)
      exact (hk i hmem).trans (hk j (Hecke.TestFunction.mem_doubleCosetSet_self K (r j))).symm
    · intro hjs
      exact absurd hj hjs
  have hsp : ⊤ ≤ Submodule.span ℂ
      (Set.range (fun i => Hecke.HeckeAlgebra.Corner.massIndicator K hK μ (r i))) := by
    rw [← Hecke.HeckeAlgebra.Corner.span_range_doubleCoset K hK μ, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨i, hi, -⟩ := hr g
    rw [SetLike.mem_coe, Hecke.HeckeAlgebra.Corner.doubleCoset_eq_of_mem K hK μ hi,
      Hecke.HeckeAlgebra.Corner.doubleCoset_eq_smul_massIndicator]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli hsp).map (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩), fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  exact heckeDistribution_massIndicator μ K hK (r i)

/-- Renard II.3.12: all seven conjuncts. -/
theorem statements : Statements.{uG} :=
  ⟨densityRealization, normalizedIndicatorRealization, localUnits, idempotentOrder, inversion,
    corner, doubleCosetBasis⟩

end Langlands.HarmonicAnalysis.Distribution.RenardHecke
