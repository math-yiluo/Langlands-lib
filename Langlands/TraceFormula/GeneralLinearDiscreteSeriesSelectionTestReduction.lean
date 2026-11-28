import Langlands.Representation.Character.WeightedTest
import Langlands.BaseChange.DeterminantSlicePseudoCoefficientStatement
import Langlands.TraceFormula.GeneralLinearLocalSelectionTestStatement
import Langlands.TraceFormula.GlobalizationLocalCoefficient
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Localization
import Langlands.BaseChange.NormNeighbourhood
import Langlands.BaseChange.RegularEllipticOpen
import Langlands.Representation.Classification.GenericEllipticCharacter
import Langlands.Representation.Classification.SegmentSpecialSquareIntegrabilityCriterionProof
import Langlands.Representation.Unitary.CentralCharacterProof
import Langlands.Representation.Unitary.Twist
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Finite.AbelianNormalBrauer
import Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Twist.AdmissibilityProof

/-!
# The square-integrable selection test for `GL_n` from normalized pseudo-coefficients

The module proves `GeneralLinearDiscreteSeriesSelectionTestStatement` from the premise
`DeterminantSlicePseudoCoefficientExistenceStatement`, which is stated in
`Langlands.BaseChange.DeterminantSlicePseudoCoefficientStatement` and proved neither there nor
here. The test function is the restriction to `|det| = 1` of a pseudo-coefficient normalized on
determinant slices. See `GeneralLinearDiscreteSeriesSelectionTestReduction.md`.
-/

noncomputable section

set_option autoImplicit false

universe u uV uW

namespace Langlands.TraceFormula.DiscreteSeriesSelection

open MeasureTheory HarmonicAnalysis Langlands.Global Langlands.QuotientIntegration
open Langlands.BaseChange
open scoped NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-! ## Sums of powers of a root of unity -/

/-- For a primitive `n`-th root of unity `ζ` and `m : ℤ`, `∑_{k < n} (ζ^m)^k` is `n` if `n ∣ m`
and `0` otherwise. -/
theorem sum_range_zpow_pow {ζ : ℂ} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (m : ℤ) :
    ∑ k ∈ Finset.range n, (ζ ^ m) ^ k = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd m).mpr h]
    simp
  · have hne : ζ ^ m ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd m).mp h')
    rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hζ.pow_eq_one, one_zpow, sub_self, zero_div]

/-! ## Characters of test functions on a totally disconnected group -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Scaling the Haar measure by `c` scales the character by `c`. -/
theorem distribution_nnreal_smul_measure (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (c : ℝ≥0) [IsFiniteMeasureOnCompacts (c • μ)]
    [(c • μ).IsMulLeftInvariant] (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (f : SchwartzBruhat G) :
    Character.distribution (c • μ) ρ hρ f = ((c : ℝ) : ℂ) * Character.distribution μ ρ hρ f := by
  have hact : Character.finiteRankIntegratedAction (c • μ) ρ hρ f =
      ((c : ℝ) : ℂ) • Character.finiteRankIntegratedAction μ ρ hρ f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change Hecke.integratedAction (c • μ) ρ hρ.1 f v =
      ((c : ℝ) : ℂ) • Hecke.integratedAction μ ρ hρ.1 f v
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro L
    rw [map_sub, sub_eq_zero, map_smul, Hecke.integratedAction_dual,
      Hecke.integratedAction_dual, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul, smul_eq_mul]
  rw [Character.distribution_apply, hact, map_smul, ← Character.distribution_apply, smul_eq_mul]

/-- On a second-countable group, the vanishing of a character at a test function does not
depend on the Haar measure. -/
theorem distribution_ne_zero_of_haar [SecondCountableTopology G]
    (μ μ₀ : Measure G) [μ.IsHaarMeasure] [μ₀.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (f : SchwartzBruhat G)
    (h : Character.distribution μ ρ hρ f ≠ 0) : Character.distribution μ₀ ρ hρ f ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ = c • μ₀ :=
    ⟨Measure.haarScalarFactor μ μ₀, Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
  subst hc
  rw [distribution_nnreal_smul_measure] at h
  exact right_ne_zero_of_mul h

/-- If unit-central elements `z` act on `φ` by `φ (z g) = χ(z)⁻¹ φ(g)` and the character of
`ρ` does not vanish at `φ`, then `z` acts on `ρ` through the same scalar `χ(z)`. -/
theorem eq_of_distribution_ne_zero_of_leftCovariant (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (φ : SchwartzBruhat G)
    (z : G) (a b : ℂ) (hb : b ≠ 0) (hφ : ∀ g, φ (z * g) = b⁻¹ * φ g)
    (hz : ∀ x, ρ z x = a • x)
    (h : Character.distribution μ ρ hρ φ ≠ 0) : a = b := by
  have htrans : Hecke.TestFunction.leftTranslate z φ = b • φ := by
    apply Subtype.ext
    funext g
    change φ (z⁻¹ * g) = b * φ g
    have := hφ (z⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have hact : Character.finiteRankIntegratedAction μ ρ hρ
      (Hecke.TestFunction.leftTranslate z φ) =
      a • Character.finiteRankIntegratedAction μ ρ hρ φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change Hecke.integratedAction μ ρ hρ.1 (Hecke.TestFunction.leftTranslate z φ) v =
      a • Hecke.integratedAction μ ρ hρ.1 φ v
    rw [Hecke.integratedAction_leftTranslate, hz]
  have h1 : Character.distribution μ ρ hρ (Hecke.TestFunction.leftTranslate z φ) =
      a * Character.distribution μ ρ hρ φ := by
    rw [Character.distribution_apply, hact, map_smul, ← Character.distribution_apply,
      smul_eq_mul]
  rw [htrans, map_smul, smul_eq_mul] at h1
  exact (mul_right_cancel₀ h h1).symm

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Let `δ` be a continuous homomorphism to `Multiplicative ℤ`, `ζ` a primitive `n`-th root of
unity and `u` a unit. If `f` vanishes at every `g` with `n ∣ δ(g)` and `δ(g) ≠ 1`, then the
weighted tests `g ↦ (ζ^k u)^{δ(g)} f(g)`, `k < n`, sum to `n` times the cut-off of `f` to
`δ = 1`. -/
theorem sum_weightedTest_eq_smul_cutoff (δ : G →* Multiplicative ℤ) (hδ : Continuous δ)
    {n : ℕ} {ζ : ℂˣ} (hζ : IsPrimitiveRoot (ζ : ℂ) n) (u : ℂˣ)
    (hloc : ∀ k : ℕ,
      IsLocallyConstant fun g : G => (((zpowersHom ℂˣ (ζ ^ k * u)).comp δ g : ℂˣ) : ℂ))
    (f : SchwartzBruhat G) (hf : ∀ g, f g ≠ 0 → (n : ℤ) ∣ (δ g).toAdd → δ g = 1) :
    ∑ k ∈ Finset.range n, Character.weightedTest ((zpowersHom ℂˣ (ζ ^ k * u)).comp δ) (hloc k) f =
      (n : ℂ) • ConcordanceLocalization.cutoff
        ((isClopen_discrete ({1} : Set (Multiplicative ℤ))).preimage hδ) f := by
  classical
  have hterm : ∀ (g : G) (k : ℕ), (((zpowersHom ℂˣ (ζ ^ k * u)).comp δ g : ℂˣ) : ℂ) =
      ((ζ : ℂ) ^ (δ g).toAdd) ^ k * (u : ℂ) ^ (δ g).toAdd := by
    intro g k
    rw [MonoidHom.comp_apply, zpowersHom_apply, mul_zpow, ← zpow_natCast ζ k, ← zpow_mul,
      mul_comm (k : ℤ), zpow_mul, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  ext g
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, Character.weightedTest_apply, hterm]
  rw [← Finset.sum_mul, ← Finset.sum_mul, sum_range_zpow_pow hζ, ConcordanceLocalization.cutoff_apply]
  have hmem : g ∈ δ ⁻¹' ({1} : Set (Multiplicative ℤ)) ↔ δ g = 1 := Iff.rfl
  by_cases h1 : (n : ℤ) ∣ (δ g).toAdd
  · by_cases h2 : δ g = 1
    · rw [ite_eq_left h1, ite_eq_left (hmem.mpr h2), h2, toAdd_one, zpow_zero, mul_one]
    · have hfg : f g = 0 := by
        by_contra hfg
        exact h2 (hf g hfg h1)
      rw [ite_eq_right (fun h => h2 (hmem.mp h)), hfg, mul_zero, mul_zero]
  · have h2 : ¬ δ g = 1 := by
      intro h2
      apply h1
      rw [h2, toAdd_one]
      exact dvd_zero _
    rw [ite_eq_right h1, ite_eq_right (fun h => h2 (hmem.mp h)), zero_mul, zero_mul, mul_zero]

end Generic

/-! ## Scaling of compatible quotient measures and of orbital integrals -/

section Scaling

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

omit [BorelSpace G] in
/-- Multiplying the Haar measure of `G` and the quotient measure by the same nonzero factor
preserves compatibility. -/
theorem isCompatible_nnreal_smul {H : Subgroup G} [MeasurableSpace H] [BorelSpace H]
    [MeasurableMul H] {μG : Measure G} {μH : Measure H} [μH.IsMulRightInvariant]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    {ν : Measure (LeftQuotient H)} (h : IsCompatible H μG μH ν) {c : ℝ≥0} (hc : c ≠ 0) :
    IsCompatible H (c • μG) μH (c • ν) where
  nonzero := by
    intro h0
    apply h.nonzero
    rw [← inv_smul_smul₀ hc ν, h0, smul_zero]
  regular := by
    have := h.regular
    infer_instance
  right_invariant g := (h.right_invariant g).smul_measure c
  averaging_integrable f hf hs := (h.averaging_integrable f hf hs).smul_measure_nnreal
  integral_formula f hf hs := by
    rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, h.integral_formula f hf hs]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- Orbital integrals are linear in the quotient measure. -/
theorem orbitalIntegral_nnreal_smul (γ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))]
    (ν : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) γ))) (c : ℝ≥0)
    (f : G → ℂ) :
    orbitalIntegral γ (c • ν) f = ((c : ℝ) : ℂ) * orbitalIntegral γ ν f := by
  rw [orbitalIntegral, orbitalIntegral, twistedOrbitalIntegral, twistedOrbitalIntegral,
    integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Scaling

/-! ## Determinant twists of generic representations -/

section GenericTwist

open GeneralLinear

universe uF

/-- A determinant twist by a character of `Fˣ` whose composite with the determinant has open
kernel preserves genericity. -/
theorem isGeneric_twist_of_isOpen_ker {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : F.Carrierˣ →* ℂˣ) {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V) :
    letI := T.topology
    IsOpen ((χ.comp (determinant (n := n + 1))).ker :
        Set (GeneralLinear (n + 1) F.Carrier)) →
      Whittaker.IsGeneric ψ n π → Whittaker.IsGeneric ψ n (twist (χ.comp determinant) π) := by
  let := T.topology
  intro hker hπ
  obtain ⟨hi, ha, ℓ, hℓ⟩ := hπ
  exact ⟨(isIrreducible_twist_iff _ π).mpr hi, (isAdmissible_twist_iff _ π hker).mpr ha,
    Whittaker.determinantTwistFunctionalEquiv ψ χ π ℓ, hℓ⟩

end GenericTwist

/-! ## Generic representations whose character does not vanish at a pseudo-coefficient -/

section Classification

open Langlands.JacquetLanglands Langlands.Classification GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private theorem padic_isEssentiallySquareIntegrable_comp_reindex'
    (T : F.TopologicalData) {a b : ℕ} (h : a = b) {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear a F.Carrier) W)
    (hρ : T.IsEssentiallySquareIntegrable ρ) :
    T.IsEssentiallySquareIntegrable (ρ.comp (GeneralLinear.reindex (R := F.Carrier)
      (finCongr h)).symm.toMonoidHom) := by
  subst b
  rw [RankinSelberg.SupercuspidalLFactorCharacterization.comp_reindex_finCongr_rfl F]
  exact hρ

set_option maxHeartbeats 800000 in
/-- Let `f` be a pseudo-coefficient of `ρ` with central character `χ` (unitary, with open
kernel) whose characters vanish on the properly induced representations. An irreducible
admissible generic representation `σ` with central character `χ` whose character does not
vanish at `f` is equivalent to `ρ`. -/
theorem nonempty_equiv_of_distribution_ne_zero (T : F.TopologicalData) (r : ℕ) :
    let := T.topology
    let := T.valuativeRel
    have := T.localField
    letI : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
    haveI : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
    ∀ (V : Type (max uF uW)) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsAdmissible ρ)
      (χ : Subgroup.center (GeneralLinear (r + 1) F.Carrier) →* ℂˣ),
      IsOpen (χ.ker : Set (Subgroup.center (GeneralLinear (r + 1) F.Carrier))) →
      (∀ z, ‖(χ z : ℂ)‖ = 1) →
      ∀ (μ : Measure (GeneralLinear (r + 1) F.Carrier)) [μ.IsHaarMeasure]
        (f : SchwartzBruhat (GeneralLinear (r + 1) F.Carrier)),
        IsPseudoCoefficient μ χ ρ hρ f →
        (∀ B : BlockShape (r + 1), 2 ≤ B.length →
          ∀ (X : Type (max uF uW)) [AddCommGroup X] [Module ℂ X]
            (Ξ : Representation ℂ (B.Levi F.Carrier) X),
            IsAdmissible Ξ → Ξ.IsIrreducible →
            ∀ h : IsAdmissible (Induction.smoothInduced (B.parabolic F.Carrier)
                (Ξ.comp (B.leviProjection F.Carrier))),
              Character.distribution μ (Induction.smoothInduced (B.parabolic F.Carrier)
                (Ξ.comp (B.leviProjection F.Carrier))) h f = 0) →
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
          (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W) (hσ : IsAdmissible σ),
          σ.IsIrreducible →
          (∃ ψ : UnitaryAdditiveCharacter F.Carrier, Whittaker.IsGeneric ψ r σ) →
          HasCentralCharacterRep σ χ →
          Character.distribution μ σ hσ f ≠ 0 → Nonempty (σ.Equiv ρ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  dsimp only
  let : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  intro V _ _ ρ hρ χ hχo hχu μ _ f hpc hind W _ _ σ hσ hirr hgen hcc hne
  obtain ⟨ψ, hgen⟩ := hgen
  have := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
  let A := SmoothRep.of σ hσ.1
  let U := SmoothRep.universeLift.{uF} A
  let e₀ := SmoothRep.universeLiftEquiv.{uF} A
  have hU : Whittaker.IsGeneric ψ r U.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r e₀).mp hgen
  obtain ⟨d, hHeads, _, ⟨fi⟩⟩ := (genericSegmentProductExhaustion T ψ r U).mp hU
  let e : σ.Equiv d.induced.representation := e₀.trans (SmoothRep.equivOfIso fi)
  have hAdm : IsAdmissible d.induced.representation := (isAdmissible_iff_of_equiv e).mp hσ
  have hne' : Character.distribution μ d.induced.representation hAdm f ≠ 0 := by
    rwa [← Character.distribution_eq_of_equiv μ hσ hAdm e]
  have hirrB : ∀ i, (d.blocks i).representation.IsIrreducible := fun i =>
    (hHeads i).choose_spec.2.1
  have hadmB : ∀ i, IsAdmissible (d.blocks i).representation := fun i =>
    (CuspidalSupport.cuspidalEmbedding F T _ (d.blocks i) (hirrB i)).1
  by_cases hproper : 1 < d.shape.length
  · exfalso
    let τ := d.shape.blockTensor (fun i => (d.blocks i).representation)
    have hτa : IsAdmissible τ := FiniteTensor.isAdmissible_external _ hadmB
    have hτi : τ.IsIrreducible := by
      have : ∀ i : Fin d.shape.length, (d.blocks i).representation.IsIrreducible := hirrB
      exact FiniteTensor.isIrreducible_external (fun i => (d.blocks i).representation) (fun i φ =>
        (admissibleSchur_scalarEndomorphism _ (hadmB i) (hirrB i) φ).exists)
    let Ξ := twist (T.leviHalfModulus d.shape) τ
    have hΞa : IsAdmissible Ξ :=
      (isAdmissible_twist_iff _ τ (T.isOpen_ker_leviHalfModulus d.shape)).mpr hτa
    have hΞi : Ξ.IsIrreducible := (isIrreducible_twist_iff _ τ).mpr hτi
    exact hne' (hind d.shape (by omega) _ Ξ hΞa hΞi hAdm)
  · have hpos : 0 < d.shape.length :=
      UnlinkedSegmentSocleProductIrreducibleProof.length_pos_of_degree F T d (Nat.succ_pos r)
    have hsingle : d.shape.length = 1 := by omega
    let i : Fin d.shape.length := ⟨0, hpos⟩
    let e₁ := T.singleBlockNormalizedProductEquiv d.shape hsingle
      (fun i => (d.blocks i).representation) (fun i => (d.blocks i).isSmooth) i
    have hi := segmentSpecialEssentialSquareIntegrability F T
      (d.segments i) (d.blocks i) (hHeads i).isSegmentQuotient
    have hess : T.IsEssentiallySquareIntegrable σ :=
      (T.isEssentiallySquareIntegrable_iff_of_equiv (e.trans e₁)).mpr
        (padic_isEssentiallySquareIntegrable_comp_reindex' T _ _ hi)
    have : Nontrivial W := Langlands.Parabolic.nontrivial_of_isIrreducible hirr
    have hsq : T.IsSquareIntegrable σ :=
      isSquareIntegrable_of_essential_of_unitaryCentralCharacter T (Nat.succ_pos r) hess
        ⟨χ, hχo, hχu, hcc⟩
    have htemp : IsTemperedRep σ :=
      (isTemperedRep_iff_isTempered T σ).mpr (Unramified.isTempered_of_isSquareIntegrable F T hsq)
    have htempU : IsTemperedRep U.representation := (isTemperedRep_iff_of_equiv e₀).mp htemp
    by_contra hno
    have hempty : IsEmpty (U.representation.Equiv ρ) := ⟨fun e' => hno ⟨e₀.trans e'⟩⟩
    have hUa : IsAdmissible U.representation := (isAdmissible_iff_of_equiv e₀).mp hσ
    have hUi : U.representation.IsIrreducible := by
      have h := hirr
      rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
      exact (LinearMap.isSimpleModule_iff_of_bijective
        (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e₀.toIntertwiningMap)
        e₀.bijective).1 h
    have hUcc : HasCentralCharacterRep U.representation χ := hcc.of_equiv e₀
    have h0 := hpc.2.2 _ U.representation hUa hUi htempU hUcc hempty
    exact hne (by rw [Character.distribution_eq_of_equiv μ hσ hUa e₀]; exact h0)

end Classification

/-! ## The valuation degree on the units of `K_v` -/

section Completion

variable {K : Type u} [Field K] [NumberField K] (v : FinitePlace K)

/-- The integer coordinate of the completion valuation on the unit group of `K_v`. -/
def unitDegree : (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map
      (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidHom)

theorem coe_unitDegree (a : (v.adicCompletion K)ˣ) :
    ((unitDegree v a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      Valued.v (a : v.adicCompletion K) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val _

theorem unitDegree_surjective : Function.Surjective (unitDegree v) := by
  intro m
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective K (m : WithZero (Multiplicative ℤ))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact WithZero.coe_ne_zero (by simpa only [map_zero] using ha.symm)
  refine ⟨Units.mk0 a ha0, WithZero.coe_injective ?_⟩
  rw [coe_unitDegree]
  exact ha

theorem unitDegree_eq_one_iff (a : (v.adicCompletion K)ˣ) :
    unitDegree v a = 1 ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  rw [← coe_unitDegree, ← WithZero.coe_one, WithZero.coe_inj]

/-- On `GL_n(K_v)`, `|det g| = 1` exactly when the determinant has valuation degree zero. -/
theorem determinantNorm_eq_one_iff {n : ℕ} (g : GeneralLinear n (v.adicCompletion K)) :
    letI : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
    haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    JacquetLanglands.determinantNorm (v.adicCompletion K) n g = 1 ↔
      unitDegree v (GeneralLinear.determinant g) = 1 := by
  let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    (CompletionPadic.topologicalData v).localField
  rw [unitDegree_eq_one_iff, ← completion_determinantNorm_eq_one_iff v g]
  have h := JacquetLanglands.determinantNorm_eq_padic (CompletionPadic.topologicalData v) n
  exact Iff.of_eq (congrArg (fun N => N g = 1) h)

end Completion

/-! ## The selection test -/

section Main

open Langlands.JacquetLanglands GeneralLinear

/-- The square-integrable selection test from elliptic pseudo-coefficients normalized on
determinant slices: the test function is the cut-off of such a pseudo-coefficient of `ρ` to
`|det| = 1`. -/
theorem generalLinearDiscreteSeriesSelectionTest_of_determinantSlicePseudoCoefficient
    (hP : DeterminantSlicePseudoCoefficientExistenceStatement.{u, max u uV uW}) :
    GeneralLinearDiscreteSeriesSelectionTestStatement.{u, uV, uW} := by
  intro K _ _ v r V _ _ ρ hρ hirr hsq
  let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    (CompletionPadic.topologicalData v).localField
  let : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := borel _
  have : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := ⟨rfl⟩
  have := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace (v.adicCompletion K) (r + 1)
  have := LocalFieldTopology.generalLinear_secondCountableTopology (v.adicCompletion K) (r + 1)
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  -- the unitary central character `χ` of `ρ`
  let := centralQuotientMeasurableSpace (v.adicCompletion K) (r + 1)
  have := centralQuotientBorelSpace (v.adicCompletion K) (r + 1)
  obtain ⟨μZ, hμZ⟩ := exists_isHaarMeasure_centralQuotient (v.adicCompletion K) (r + 1)
  obtain ⟨c, -⟩ := (hsq μZ).2
  let χ := c.character
  have hcc : HasCentralCharacterRep ρ χ := c.acts
  -- the pseudo-coefficient of the universe lift of `ρ`
  let ρL := universeLiftRepresentation.{max u uW} ρ
  have eρ : ρ.Equiv ρL := universeLiftEquiv ρ
  have hρL : IsAdmissible ρL := (isAdmissible_universeLift_iff ρ).mpr hρ
  have hirrL : ρL.IsIrreducible := (isIrreducible_universeLift_iff ρ).mpr hirr
  have hsqL : IsSquareIntegrable ρL := (isSquareIntegrable_iff_of_equiv eρ).mp hsq
  have hccL : HasCentralCharacterRep ρL χ := hcc.of_equiv eρ
  let μ₀ : Measure (GeneralLinear (r + 1) (v.adicCompletion K)) := Measure.haar
  obtain ⟨f, hpc, hind, hnorm, U₀, hU₀, horb⟩ := hP (v.adicCompletion K) (r + 1)
    (Nat.succ_pos r) (ULift.{max u uW} V) ρL hρL hirrL hsqL χ hccL μ₀
  -- the determinant slice
  let δ : GeneralLinear (r + 1) (v.adicCompletion K) →* Multiplicative ℤ :=
    (unitDegree v).comp determinant
  have hδnorm : ∀ g, δ g = 1 ↔ determinantNorm (v.adicCompletion K) (r + 1) g = 1 :=
    fun g => (determinantNorm_eq_one_iff v g).symm
  have hδopen : IsOpen (δ.ker : Set (GeneralLinear (r + 1) (v.adicCompletion K))) := by
    have : (δ.ker : Set (GeneralLinear (r + 1) (v.adicCompletion K))) =
        ((determinantNorm (v.adicCompletion K) (r + 1)).ker : Set _) := by
      ext g
      exact hδnorm g
    rw [this]
    exact isOpen_determinantNorm_ker _ _
  have hδc : Continuous δ := Weil.continuous_of_open_kernel δ hδopen
  let φ := ConcordanceLocalization.cutoff
    ((isClopen_discrete ({1} : Set (Multiplicative ℤ))).preimage hδc) f
  refine ⟨φ, ?_, ?_⟩
  · intro W _ _ π hπ hirrπ hunit hgen μ _ hne
    obtain ⟨ψ, hgen⟩ := hgen
    -- the unitary central character `ω` of `π` agrees with `χ` on the central `G¹`
    obtain ⟨cπ⟩ := unitarizableCentralCharacter π hπ hirrπ hunit
    let ω := cπ.character
    have hφcov : ∀ z : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K)), δ z = 1 →
        ∀ g, φ (z * g) = (χ z : ℂ)⁻¹ * φ g := by
      intro z hz g
      have hdet : δ ((z : GeneralLinear (r + 1) (v.adicCompletion K)) * g) = δ g := by
        rw [map_mul, hz, one_mul]
      have hzn : determinantNorm (v.adicCompletion K) (r + 1) z = 1 := (hδnorm z).mp hz
      change ConcordanceLocalization.cutoff _ f (_ * g) =
        (χ z : ℂ)⁻¹ * ConcordanceLocalization.cutoff _ f g
      rw [ConcordanceLocalization.cutoff_apply, ConcordanceLocalization.cutoff_apply]
      have hmem : ((z : GeneralLinear (r + 1) (v.adicCompletion K)) * g ∈
          δ ⁻¹' ({1} : Set (Multiplicative ℤ))) ↔ g ∈ δ ⁻¹' ({1} : Set (Multiplicative ℤ)) := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hdet]
      by_cases hg : g ∈ δ ⁻¹' ({1} : Set (Multiplicative ℤ))
      · rw [ite_eq_left (hmem.mpr hg), ite_eq_left hg, hnorm.1 z hzn g]
      · rw [ite_eq_right (fun h => hg (hmem.mp h)), ite_eq_right hg, mul_zero]
    have hωχ : ∀ z : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K)), δ z = 1 →
        ω z = χ z := by
      intro z hz
      apply Units.ext
      exact eq_of_distribution_ne_zero_of_leftCovariant μ π hπ φ z (ω z) (χ z) (χ z).ne_zero
        (hφcov z hz) (cπ.acts z) hne
    -- a central element of degree `r + 1`
    obtain ⟨a₁, ha₁⟩ := unitDegree_surjective v (Multiplicative.ofAdd (1 : ℤ))
    let s₁ : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K)) := scalarToCenter a₁
    have hδs₁ : δ s₁ = Multiplicative.ofAdd ((r + 1 : ℕ) : ℤ) := by
      change unitDegree v (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a₁)) = _
      rw [Matrix.GeneralLinearGroup.det_scalar, map_pow, ha₁, Fintype.card_fin, ← ofAdd_nsmul,
        nsmul_eq_mul, mul_one]
    have hdiv : ∀ z : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K)),
        ((r + 1 : ℕ) : ℤ) ∣ (δ z).toAdd := by
      intro z
      have hz := z.property
      simp only [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨a, ha⟩ := hz
      refine ⟨(unitDegree v a).toAdd, ?_⟩
      change (unitDegree v (Matrix.GeneralLinearGroup.det
        (z : GeneralLinear (r + 1) (v.adicCompletion K)))).toAdd = _
      rw [← ha, Matrix.GeneralLinearGroup.det_scalar, map_pow, toAdd_pow, Fintype.card_fin,
        nsmul_eq_mul]
    -- an `(r+1)`-th root `c'` of `χ(s₁)/ω(s₁)` and a primitive `(r+1)`-th root of unity
    let cc : ℂˣ := χ s₁ / ω s₁
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq (cc : ℂ) (Nat.succ_pos r)
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero r)] at hc'
      exact cc.ne_zero hc'.symm
    let c'u : ℂˣ := Units.mk0 c' hc'0
    have hζ := Complex.isPrimitiveRoot_exp (r + 1) (Nat.succ_ne_zero r)
    let ζu : ℂˣ := Units.mk0 _ (hζ.ne_zero (Nat.succ_ne_zero r))
    have hζu : IsPrimitiveRoot (ζu : ℂ) (r + 1) := hζ
    have hζnorm : ‖(ζu : ℂ)‖ = 1 := hζu.norm'_eq_one (Nat.succ_ne_zero r)
    have hc'norm : ‖(c'u : ℂ)‖ = 1 := by
      have h1 : ‖(c'u : ℂ)‖ ^ (r + 1) = 1 := by
        change ‖c'‖ ^ (r + 1) = 1
        rw [← norm_pow, hc', Units.val_div_eq_div_val, norm_div, c.norm_eq_one,
          cπ.norm_eq_one, div_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero r)).mp h1
    -- the characters `λ_k = (ζ^k c')^{deg}` of `K_vˣ`
    let lam : ℕ → (v.adicCompletion K)ˣ →* ℂˣ :=
      fun k => (zpowersHom ℂˣ (ζu ^ k * c'u)).comp (unitDegree v)
    have hloc : ∀ k : ℕ, IsLocallyConstant fun g : GeneralLinear (r + 1) (v.adicCompletion K) =>
        (((zpowersHom ℂˣ (ζu ^ k * c'u)).comp δ g : ℂˣ) : ℂ) := fun k =>
      (IsLocallyConstant.of_discrete
        (fun m : Multiplicative ℤ => ((zpowersHom ℂˣ (ζu ^ k * c'u) m : ℂˣ) : ℂ))).comp_continuous
        hδc
    have hker : ∀ k : ℕ, IsOpen (((lam k).comp (determinant (n := r + 1))).ker :
        Set (GeneralLinear (r + 1) (v.adicCompletion K))) := by
      intro k
      apply Subgroup.isOpen_mono _ hδopen
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      change zpowersHom ℂˣ (ζu ^ k * c'u) (δ g) = 1
      rw [hg, map_one]
    -- lift `π` to the carrier universe of the classification
    let πL := universeLiftRepresentation.{uV} π
    have eπ : π.Equiv πL := universeLiftEquiv π
    have hπL : IsAdmissible πL := (isAdmissible_universeLift_iff π).mpr hπ
    have hirrπL : πL.IsIrreducible := (isIrreducible_universeLift_iff π).mpr hirrπ
    have hgenL : Whittaker.IsGeneric ψ r πL := (Whittaker.isGeneric_iff_of_equiv ψ r eπ).mp hgen
    have hneL : Character.distribution μ πL hπL φ ≠ 0 := by
      rwa [← Character.distribution_eq_of_equiv μ hπ hπL eπ]
    -- `(r+1) φ = ∑_k λ_k(det) f`, so some twist of `π` has nonvanishing character at `f`
    have hf : ∀ g, f g ≠ 0 → ((r + 1 : ℕ) : ℤ) ∣ (δ g).toAdd → δ g = 1 := by
      intro g hfg hj
      obtain ⟨j, hj⟩ := hj
      have h1 : δ (((s₁ ^ (-j) : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K))) :
          GeneralLinear (r + 1) (v.adicCompletion K)) * g) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, Subgroup.coe_zpow, map_zpow, hδs₁, toAdd_mul, toAdd_zpow, hj, toAdd_ofAdd,
          toAdd_one, smul_eq_mul]
        ring
      exact (hδnorm g).mpr (hnorm.2 _ g hfg ((hδnorm _).mp h1))
    have hsum := congrArg (Character.distribution μ πL hπL)
      (sum_weightedTest_eq_smul_cutoff δ hδc hζu c'u hloc f hf)
    rw [map_sum, map_smul, smul_eq_mul] at hsum
    have hsum_ne : ∑ k ∈ Finset.range (r + 1), Character.distribution μ πL hπL
        (Character.weightedTest ((zpowersHom ℂˣ (ζu ^ k * c'u)).comp δ) (hloc k) f) ≠ 0 := by
      rw [hsum]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)) hneL
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    let σ := twist ((lam k).comp (determinant (n := r + 1))) πL
    have hσ : IsAdmissible σ := (isAdmissible_twist_iff _ πL (hker k)).mpr hπL
    have hσirr : σ.IsIrreducible := (isIrreducible_twist_iff _ πL).mpr hirrπL
    have hσne : Character.distribution μ₀ σ hσ f ≠ 0 := by
      apply distribution_ne_zero_of_haar μ μ₀ σ hσ f
      have h := Character.distribution_twist_weightedTest μ πL hπL ((lam k).comp (determinant (n := r + 1))) (hloc k)
        hσ f
      rw [h]
      exact hk
    -- the central character of `σ` is `χ`
    have hΛs₁ : ((lam k).comp (determinant (n := r + 1))) (s₁ : GeneralLinear (r + 1)
        (v.adicCompletion K)) * ω s₁ = χ s₁ := by
      change zpowersHom ℂˣ (ζu ^ k * c'u) (δ s₁) * ω s₁ = χ s₁
      have hζ1 : ζu ^ (r + 1) = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hζu.pow_eq_one)
      have hc'1 : c'u ^ (r + 1) = cc := Units.ext (by
        rw [Units.val_pow_eq_pow_val]
        exact hc')
      rw [hδs₁, zpowersHom_apply, toAdd_ofAdd, zpow_natCast, mul_pow, ← pow_mul, mul_comm k,
        pow_mul, hζ1, one_pow, one_mul, hc'1, div_mul_cancel]
    have hcentral : ∀ z : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K)),
        ((lam k).comp (determinant (n := r + 1))) (z : GeneralLinear (r + 1)
          (v.adicCompletion K)) * ω z = χ z := by
      intro z
      obtain ⟨j, hj⟩ := hdiv z
      obtain ⟨z₀, hz₀, rfl⟩ : ∃ z₀ : Subgroup.center (GeneralLinear (r + 1) (v.adicCompletion K)),
          δ z₀ = 1 ∧ z = z₀ * s₁ ^ j := by
        refine ⟨z * s₁ ^ (-j), ?_, ?_⟩
        · apply Multiplicative.toAdd.injective
          rw [Subgroup.coe_mul, map_mul, Subgroup.coe_zpow, map_zpow, hδs₁, toAdd_mul, toAdd_zpow,
            hj, toAdd_ofAdd, toAdd_one, smul_eq_mul]
          ring
        · rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      have hΛz₀ : ((lam k).comp (determinant (n := r + 1))) (z₀ : GeneralLinear (r + 1)
          (v.adicCompletion K)) = 1 := by
        change zpowersHom ℂˣ (ζu ^ k * c'u) (δ z₀) = 1
        rw [hz₀, map_one]
      rw [Subgroup.coe_mul, Subgroup.coe_zpow, map_mul, map_zpow, map_mul, map_zpow, map_mul,
        map_zpow, hΛz₀, hωχ z₀ hz₀, ← hΛs₁, mul_zpow, one_mul]
      ac_rfl
    have hσcc : HasCentralCharacterRep σ χ := by
      intro z w
      apply ULift.ext
      change ((((lam k).comp (determinant (n := r + 1))) (z : GeneralLinear (r + 1)
          (v.adicCompletion K)) : ℂˣ) : ℂ) • (π z w.down) = (χ z : ℂ) • w.down
      rw [cπ.acts z w.down, smul_smul, ← Units.val_mul, hcentral z]
    -- classification: `σ` is equivalent to the lift of `ρ`
    have K1 := nonempty_equiv_of_distribution_ne_zero.{max uV uW, u}
      (CompletionPadic.topologicalData v) r (ULift.{max u uW} V) ρL hρL χ c.isOpen_ker
      c.norm_eq_one
    obtain ⟨e⟩ := @K1 μ₀ (by exact (inferInstance : μ₀.IsHaarMeasure)) f hpc hind
      (ULift.{uV} W) _ _ σ hσ hσirr
      ⟨ψ, isGeneric_twist_of_isOpen_ker (CompletionPadic.topologicalData v) ψ (lam k) πL (hker k)
        hgenL⟩ hσcc hσne
    -- conclusion with the unramified unitary character `λ_k⁻¹`
    have hnormu : ‖((ζu ^ k * c'u : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hζnorm, hc'norm, one_pow,
        one_mul]
    refine ⟨(lam k)⁻¹, ?_, ?_, ?_⟩
    · intro t ht
      rw [MonoidHom.inv_apply, inv_eq_one]
      change zpowersHom ℂˣ (ζu ^ k * c'u) (unitDegree v t) = 1
      rw [(unitDegree_eq_one_iff v t).mpr ht, map_one]
    · intro t
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv]
      change ‖((zpowersHom ℂˣ (ζu ^ k * c'u) (unitDegree v t) : ℂˣ) : ℂ)‖⁻¹ = 1
      rw [zpowersHom_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hnormu, one_zpow, inv_one]
    · exact ⟨((twistEquiv ((lam k)⁻¹.comp (determinant (n := r + 1))) eρ).trans
        (twistEquiv ((lam k)⁻¹.comp (determinant (n := r + 1))) e.symm)).trans
        ((equivOfRepresentationEq
          (twist_inv_twist ((lam k).comp (determinant (n := r + 1))) πL)).trans eπ.symm)⟩
  · -- orbital nonvanishing on the regular elliptic elements near `1` with `|det| = 1`
    have hN : interior (U₀ ∩ (δ.ker : Set (GeneralLinear (r + 1) (v.adicCompletion K)))) ∈
        nhds (1 : GeneralLinear (r + 1) (v.adicCompletion K)) :=
      interior_mem_nhds.mpr (Filter.inter_mem hU₀ (hδopen.mem_nhds (one_mem _)))
    obtain ⟨γ₀, hγ₀, hreg₀⟩ :=
      (normNeighbourhood.{u, 0} (v.adicCompletion K) (r + 1)).1 (Nat.succ_pos r) _ hN
    refine ⟨interior (U₀ ∩ (δ.ker : Set (GeneralLinear (r + 1) (v.adicCompletion K)))) ∩
        {g | IsRegularElliptic g},
      isOpen_interior.inter (isOpen_regularElliptic _ _), ⟨γ₀, hγ₀, hreg₀⟩, ?_⟩
    rintro γ ⟨hγ, hreg⟩ μ _ μγ _ _ νγ hνγ
    have hγ' := interior_subset hγ
    have hδγ : δ γ ∈ ({1} : Set (Multiplicative ℤ)) := hγ'.2
    have hcut := ConcordanceLocalization.orbital_cutoff (MonoidHom.id _) δ hδc
      (isClopen_discrete ({1} : Set (Multiplicative ℤ))) (fun x g => by simp) γ νγ f
    rw [ite_eq_left hδγ] at hcut
    change orbitalIntegral γ νγ φ = orbitalIntegral γ νγ f at hcut
    rw [hcut]
    obtain ⟨a, ha0, ha⟩ : ∃ a : ℝ≥0, a ≠ 0 ∧ μ = a • μ₀ :=
      ⟨Measure.haarScalarFactor μ μ₀, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne',
        Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
    subst ha
    have hcomp : IsCompatible (glCentralizer γ) μ₀ μγ (a⁻¹ • νγ) := by
      have h := isCompatible_nnreal_smul hνγ (inv_ne_zero ha0)
      rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h
      exact h
    have h := horb γ hγ'.1 hreg μγ _ hcomp
    rw [orbitalIntegral_nnreal_smul] at h
    exact right_ne_zero_of_mul h

/-- The square-integrable selection test for `GL_n` at a finite place follows from the existence
of elliptic pseudo-coefficients normalized on determinant slices (with carriers in the universe
`max u uV uW`). -/
def GeneralLinearDiscreteSeriesSelectionTestReductionStatement : Prop :=
  DeterminantSlicePseudoCoefficientExistenceStatement.{u, max u uV uW} →
    GeneralLinearDiscreteSeriesSelectionTestStatement.{u, uV, uW}

theorem generalLinearDiscreteSeriesSelectionTestReduction :
    GeneralLinearDiscreteSeriesSelectionTestReductionStatement.{u, uV, uW} :=
  fun hP => generalLinearDiscreteSeriesSelectionTest_of_determinantSlicePseudoCoefficient hP

end Main

end Langlands.TraceFormula.DiscreteSeriesSelection
