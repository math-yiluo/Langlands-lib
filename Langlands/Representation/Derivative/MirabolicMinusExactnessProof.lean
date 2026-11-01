import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof

/-!
# Exactness of the four actual mirabolic minus functors

The radical inherits compact-subgroup containment from its closed inclusion in
the upper-unipotent group. Character-localization exactness then applies, and
continuous pullback and determinant twisting preserve the underlying linear maps.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open CategoryTheory GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Topology

universe uF uV uG uH uK

private theorem radicalToUpperUnipotent_isClosedEmbedding
    {F : Type uF} [Field F] [TopologicalSpace F] [T2Space F] (n : ℕ) :
    IsClosedEmbedding (radicalToUpperUnipotent (n := n) (F := F)) := by
  apply IsClosedEmbedding.of_comp
    (g := fun g : GeneralLinear.upperUnipotent (n + 1) F => g.val)
    IsEmbedding.subtypeVal
  exact (GeneralLinear.Mirabolic.isClosed (n := n) (F := F)).isClosedEmbedding_subtypeVal.comp
    (radical_isClosed (n := n) (F := F)).isClosedEmbedding_subtypeVal

/-- Every compact subset of the actual mirabolic radical is contained in a compact
subgroup, for the supplied field topology and in every rank, including zero. -/
theorem radical_isLimitOfCompactSubgroups {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    Jacquet.Localization.IsLimitOfCompactSubgroups (radical n F.Carrier) := by
  let := T.topology
  let := T.fieldT2
  let f := radicalToUpperUnipotent (n := n) (F := F.Carrier)
  have hf : IsClosedEmbedding f := radicalToUpperUnipotent_isClosedEmbedding n
  intro C hC
  obtain ⟨K, hK, hCK⟩ :=
    GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1)
      (f '' C) (hC.image hf.continuous)
  refine ⟨K.comap f, hf.isCompact_preimage hK, ?_⟩
  intro c hc
  exact hCK ⟨c, hc, rfl⟩

private theorem character_isLocallyConstant_of_isOpen_ker
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹' (χ.ker : Set G),
    hχ.preimage (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change χ (y * x⁻¹) = 1 at hy
    have heq : χ y = χ x := mul_inv_eq_one.mp (by
      simpa only [map_mul, map_inv] using hy)
    exact congrArg (fun z : ℂˣ => (z : ℂ)) heq

private theorem smoothLocalization_mapsShortExact
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθloc : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : Jacquet.Localization.IsInvariant U M hMU θ) :
    MapsShortExactIntertwiners
      (Jacquet.Localization.smoothFunctor.{0, uG, uV} U θ M hMU hθ) := by
  intro A B C i q hi hq hex
  exact (Jacquet.Localization.characterLocalizationExactness
    (G := G) (V := A) (W := B) (X := C)).2
      U hU θ hθloc M hMU hθ A.representation B.representation C.representation
      (SmoothRep.hom i) (SmoothRep.hom q) hi hq hex B.isSmooth

private theorem mapsShortExact_comp_pullback
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H]
    {K : Type uK} [Group K] [TopologicalSpace K]
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    (hJ : MapsShortExactIntertwiners J) (φ : K →* H) (hφ : Continuous φ) :
    MapsShortExactIntertwiners (J ⋙ continuousPullbackFunctor φ hφ) := by
  intro A B C i q hi hq hex
  exact hJ A B C i q hi hq hex

private theorem mapsShortExact_comp_twist
    {G : Type uG} [Group G] [TopologicalSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H]
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    (hJ : MapsShortExactIntertwiners J) (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H)) :
    MapsShortExactIntertwiners (J ⋙ SmoothRep.twistFunctor χ hχ) := by
  intro A B C i q hi hq hex
  exact hJ A B C i q hi hq hex

private theorem psiMinusUnnormalized_mapsShortExact {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    MapsShortExactIntertwiners (psiMinusUnnormalized.{uV} T n) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  exact mapsShortExact_comp_pullback _
    (smoothLocalization_mapsShortExact (radical n F.Carrier)
      (radical_isLimitOfCompactSubgroups F T n) 1 (IsLocallyConstant.const (1 : ℂ))
      (leviSubgroup n F.Carrier) leviSubgroup_le_normalizer
      (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer))
    (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (leviContinuousEquiv (n := n) (F := F.Carrier)).continuous

private theorem phiMinusUnnormalized_mapsShortExact {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    MapsShortExactIntertwiners (phiMinusUnnormalized.{uV} T ψ n) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact mapsShortExact_comp_pullback _
    (smoothLocalization_mapsShortExact (radical (n + 1) F.Carrier)
      (radical_isLimitOfCompactSubgroups F T (n + 1)) (T.mirabolicTheta ψ n)
      (character_isLocallyConstant_of_isOpen_ker _ (T.mirabolicTheta_isOpen_ker ψ n))
      (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
      (theta_isInvariant ψ n))
    (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
    (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous

/-- The four actual mirabolic minus functors preserve short exact sequences of
underlying intertwiners, with independent field and representation universes. -/
theorem minusExactness {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MinusExactnessStatement.{uF, uV} F T := by
  let := T.topology
  refine ⟨psiMinusUnnormalized_mapsShortExact F T,
    phiMinusUnnormalized_mapsShortExact F T, ?_, ?_⟩
  · intro n
    exact mapsShortExact_comp_twist _ (psiMinusUnnormalized_mapsShortExact F T n)
      (psiMinusCharacter T n) (isOpen_ker_psiMinusCharacter T n)
  · intro n ψ
    exact mapsShortExact_comp_twist _ (phiMinusUnnormalized_mapsShortExact F T n ψ)
      (phiMinusCharacter T n) (isOpen_ker_phiMinusCharacter T n)

end Langlands.Derivative.Mirabolic
