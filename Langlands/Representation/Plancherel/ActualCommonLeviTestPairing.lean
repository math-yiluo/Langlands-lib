import Langlands.Representation.Plancherel.ActualCommonLeviTestIntegral
import Langlands.Representation.Plancherel.ActualCommonLeviTestSections

/-! # Evaluation of each common-Levi adjunction test on its integral domain -/

noncomputable section

set_option maxHeartbeats 1300000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj ENNReal NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviIwasawa

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor OppositeIntertwiningDualAdjunction Langlands.QuotientIntegration
open StandardIntertwining.OrderedSubgroupFactorization

section RealIntegral

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

private theorem complexIntegral_eq_lintegral_toReal (μX : Measure X) (f : X → ℝ≥0∞)
    (hf : ∀ x, f x ≠ ⊤) (hi : Integrable (fun x => ((f x).toReal : ℂ)) μX) :
    (∫ x, ((f x).toReal : ℂ) ∂μX) = ((∫⁻ x, f x ∂μX).toReal : ℂ) ∧
      (∫⁻ x, f x ∂μX) ≠ ⊤ := by
  have hr : Integrable (fun x => (f x).toReal) μX := by
    have h := hi.re
    change Integrable (fun x => ((f x).toReal : ℂ).re) μX at h
    simpa only [Complex.ofReal_re] using h
  have hn : 0 ≤ᵐ[μX] fun x => (f x).toReal :=
    ae_of_all μX fun x => ENNReal.toReal_nonneg
  have he : (fun x => ENNReal.ofReal (f x).toReal) = f :=
    funext fun x => ENNReal.ofReal_toReal (hf x)
  constructor
  · rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae hn hr.aestronglyMeasurable, he]
  · have hlt : (∫⁻ x, f x ∂μX) < ⊤ := by
      rw [← he]
      exact (hasFiniteIntegral_iff_ofReal hn).mp hr.hasFiniteIntegral
    exact hlt.ne

private theorem integral_eq_of_iterated_lintegral (μX : Measure X) (μY : Measure Y)
    (f : X → Y → ℝ≥0∞) (g : X → ℂ) (hg : Integrable g μX)
    (hf : ∀ x y, f x y ≠ ⊤)
    (hrow : ∀ x, Integrable (fun y => ((f x y).toReal : ℂ)) μY ∧
      (∫ y, ((f x y).toReal : ℂ) ∂μY) = g x) :
    (∫ x, g x ∂μX) = ((∫⁻ x, ∫⁻ y, f x y ∂μY ∂μX).toReal : ℂ) := by
  have h x := complexIntegral_eq_lintegral_toReal μY (f x) (hf x) (hrow x).1
  have he : g = fun x => ((∫⁻ y, f x y ∂μY).toReal : ℂ) :=
    funext fun x => (hrow x).2.symm.trans (h x).1
  rw [he] at hg ⊢
  exact (complexIntegral_eq_lintegral_toReal μX _ (fun x => (h x).2) hg).1

end RealIntegral

section Representatives

variable {X : Type u} [Group X] [TopologicalSpace X]
  [LocallyCompactSpace X] [NonarchimedeanGroup X]
  {P P' M U V : Subgroup X} (d : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set X))
  (d' : IsSemidirectDecomposition P' M V) (hV : IsClosed (V : Set X))
  {T : SmoothRep.{0, u, uV} ℂ M} {ξ ξ' : M →* ℂˣ}
  {hξ : IsOpen (ξ.ker : Set M)} {hξ' : IsOpen (ξ'.ker : Set M)}
  (φ : (DynamicNormalization.leviTwistedInductionFunctor d hU).obj (T.twist ξ hξ))
  (φ' : (DynamicNormalization.leviTwistedInductionFunctor d' hV).obj (T.contragredient.twist ξ' hξ'))

private theorem forward_probe_mk (k : X) (u : V) :
    (twistDualFunctional (A := T) ξ hξ
      (eval P' (leviInflatedInducingRepresentation d' hV (T.contragredient.twist ξ' hξ')) φ' k)).val
        (integrand d hU V (T.twist ξ hξ) k φ (Quotient.mk _ u)) =
      dualIntegrand d hU d' hV φ φ' ((u : X) * k) := by
  rw [integrand_mk]
  unfold dualIntegrand
  rw [source_unipotent_invariant d' hV (T.contragredient.twist ξ' hξ') φ' u k]
  rfl

private theorem reverse_probe_mk (k : X) (u : U) :
    (twistEvaluationFunctional (A := T) ξ' hξ'
      (eval P (leviInflatedInducingRepresentation d hU (T.twist ξ hξ)) φ k)).val
        (integrand d' hV U (T.contragredient.twist ξ' hξ') k φ' (Quotient.mk _ u)) =
      dualIntegrand d hU d' hV φ φ' ((u : X) * k) := by
  rw [integrand_mk]
  unfold dualIntegrand
  rw [source_unipotent_invariant d hU (T.twist ξ hξ) φ u k]

end Representatives

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  Langlands.HaarModulus.subgroupMeasurableSpace
  Langlands.HaarModulus.subgroupBorelSpace
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance testPairingAmbientMeasurable : MeasurableSpace (RationalPoint F G.X) := borel _
local instance testPairingAmbientBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance testPairingAmbientSecondCountable : SecondCountableTopology (RationalPoint F G.X) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F G
local instance testPairingSubgroupSecondCountable (S : Subgroup (RationalPoint F G.X)) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set (RationalPoint F G.X))
local instance testPairingRadicalLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (radical φ) := (radical_isClosed φ).locallyCompactSpace
local instance testPairingLeviLocallyCompact (φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (levi φ) := (levi_isClosed φ).locallyCompactSpace
local instance testPairingIntersectionLocallyCompact (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace ((radical ψ).subgroupOf (radical φ)) :=
  ((radical_isClosed ψ).preimage continuous_subtype_val).locallyCompactSpace
local instance testPairingIntersectionSecondCountable (ψ φ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    SecondCountableTopology ((radical ψ).subgroupOf (radical φ)) :=
  TopologicalSpace.Subtype.secondCountableTopology
    ((radical ψ).subgroupOf (radical φ) : Set (radical φ))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (t : CompactAdjunctionTest χ K ψ hψ ψ' hψ' A)
  (z : unramifiedCharacters (normCharacters χ))

local notation "Γ" => RationalPoint F G.X
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "I" => (radical ψ).subgroupOf (radical ψ')
local notation "incl" => intersectionAmbientHom (radical ψ) (radical ψ')
local notation "η" => parameterTransport χ z
local notation "η'" => parameterTransport χ z⁻¹
local notation "Az" => twistObject χ z A
local notation "Ad" => twistObject χ z⁻¹ A.contragredient
local notation "hη" => unramifiedCharacter_isOpen_ker (leviNormCharacters χ) η
local notation "hη'" => unramifiedCharacter_isOpen_ker (leviNormCharacters χ) η'
local notation "μG" => RankinSelberg.normalizedCompactOpenHaar K hK
local notation "ν'" => pairQuotientMeasure K hK ψ ψ'
local notation "ν₀" => pairQuotientMeasure K hK ψ' ψ
local notation "f" => sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z
local notation "f'" => targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z
local notation "eval₀" => eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ Az)
local notation "eval₁" => eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ Ad)
local notation "X₁" => QuotientSpace (U := radical ψ) (radical ψ')
local notation "X₀" => QuotientSpace (U := radical ψ') (radical ψ)
local notation "R₁" => normalizedQuotientTestAverage χ K hK t.subgroup ψ ψ'
local notation "R₀" => normalizedQuotientTestAverage χ K hK t.subgroup ψ' ψ

/-- The exact real, positive value of the original bilinear compact test, viewed in `ℂ`. -/
def compactAdjunctionTestValue : ℂ :=
  ((compactTestMass χ K hK t.subgroup ψ ψ').toReal : ℂ)

/-- The two compact test values detect a nonzero adjunction scale. -/
theorem compactAdjunctionTestValue_ne_zero :
    compactAdjunctionTestValue χ K hK ψ hψ ψ' hψ' A t ≠ 0 := by
  have h := compactTestMass_finite_positive χ K hK t.subgroup ψ ψ' hψ' t.isCompact_subgroup
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos h.1 h.2).ne'

private theorem normalizedTestAverage_finite
    (hG : IsConnectedReductive G) (g : Γ) :
    normalizedTestAverage χ K hK t.subgroup ψ ψ' g ≠ ⊤ := by
  by_cases h : ∃ (m : levi χ) (x : I) (q : t.subgroup), g = (m : Γ) * incl x * (q : Γ)
  · obtain ⟨m, x, q, rfl⟩ := h
    rw [normalizedTestAverage_factor χ K hK t.subgroup ψ ψ' hψ hψ' hG t.isCompact_subgroup]
    exact ENNReal.coe_ne_top
  · rw [normalizedTestAverage_eq_zero χ K hK t.subgroup ψ ψ' hψ hψ' h]
    exact ENNReal.zero_ne_top

private theorem normalizedTestAverage_swap (g : Γ) :
    normalizedTestAverage χ K hK t.subgroup ψ ψ' g =
      normalizedTestAverage χ K hK t.subgroup ψ' ψ g := by
  let μM := Haar.subgroupCompactOpenHaar K hK (levi χ) (levi_isClosed χ)
  exact congrArg₂ (fun a b : ℝ≥0∞ => a⁻¹ * b)
    (compactTestAverage_swap K hK hU₀ hU₁ t.subgroup μM 1)
    (compactTestAverage_swap K hK hU₀ hU₁ t.subgroup μM g)

section Forward

local notation "Jvalue[" j "]" => eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ Az) j

/-- The original pairing of a forward value with the target test at one group point. -/
def forwardTestPairingIntegrand
    (test : CompactAdjunctionTest χ K ψ hψ ψ' hψ' A)
    (w : unramifiedCharacters (normCharacters χ))
    (j : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj (twistObject χ w A))
    (k : Γ) : ℂ :=
  smoothDualPairing A.representation
    (eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ (twistObject χ w⁻¹ A.contragredient))
      (targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A test w) k)
    (eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ (twistObject χ w A)) j k)

local notation "Φ[" j "]" => forwardTestPairingIntegrand χ K ψ hψ ψ' hψ' A t z j

private theorem forward_testPairing_slice
    (j : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj Az)
    (hG : IsConnectedReductive G) (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (hj : HasIntegral h₀ hU₀ (radical ψ') Az ν' f Jvalue[j]) (k : Γ) :
    Integrable (fun x : X₁ => ((R₁ k x).toReal : ℂ)) ν' ∧
      (∫ x : X₁, ((R₁ k x).toReal : ℂ) ∂ν') = Φ[j] k := by
  let ℓ := twistDualFunctional (A := A) (η).val.toMonoidHom hη (eval₁ f' k)
  have htest := hj k ℓ
  have he : (fun x : X₁ => ℓ.val (integrand h₀ hU₀ (radical ψ') Az k f x)) =
      fun x => ((R₁ k x).toReal : ℂ) := by
    funext x
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    change _ = ((normalizedTestAverage χ K hK t.subgroup ψ ψ' ((u : Γ) * k)).toReal : ℂ)
    exact (forward_probe_mk h₀ hU₀ h₁ hU₁ (T := A)
      (ξ := (η).val.toMonoidHom) (ξ' := (η').val.toMonoidHom) (hξ := hη) (hξ' := hη') f f' k u).trans
      (dualIntegrand_testSections_eq χ K ψ hψ ψ' hψ' A t z hK hG hδ ((u : Γ) * k))
  rw [he] at htest
  exact ⟨htest.1, htest.2⟩

/-- The original compact test of the forward integral has the exact common value
on its own convergence domain. -/
theorem forward_testPairing_eq
    (j : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj Az)
    (hG : IsConnectedReductive G) (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (hj : HasIntegral h₀ hU₀ (radical ψ') Az ν' f Jvalue[j]) :
    (∫ k in (K : Set Γ), Φ[j] k ∂μG) = compactAdjunctionTestValue χ K hK ψ hψ ψ' hψ' A t := by
  have hcont : Continuous Φ[j] :=
    (bilinearPairing_isLocallyConstant (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ Az)
      (leviInflatedInducingRepresentation h₁ hU₁ Ad) (smoothDualPairing A.representation) f' j).continuous
  have hi : Integrable Φ[j] ((μG).restrict (K : Set Γ)) := hcont.continuousOn.integrableOn_compact hK
  have hf (k : Γ) (x : X₁) : R₁ k x ≠ ⊤ := by
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    exact normalizedTestAverage_finite χ K hK ψ hψ ψ' hψ' A t hG ((u : Γ) * k)
  have hs := forward_testPairing_slice χ K hK ψ hψ ψ' hψ' A t z j hG hδ hj
  have he := integral_eq_of_iterated_lintegral ((μG).restrict (K : Set Γ)) ν' R₁ Φ[j] hi hf hs
  rw [he, lintegral_normalizedQuotientTestAverage χ K hK t.subgroup ψ ψ' hψ' hψ'K t.isCompact_subgroup]
  rfl

end Forward

section Reverse

local notation "Jvalue'[" j' "]" => eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ Ad) j'

/-- The original pairing of a reverse-dual value with the source test at one group point. -/
def reverseTestPairingIntegrand
    (test : CompactAdjunctionTest χ K ψ hψ ψ' hψ' A)
    (w : unramifiedCharacters (normCharacters χ))
    (j' : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (twistObject χ w⁻¹ A.contragredient))
    (k : Γ) : ℂ :=
  smoothDualPairing A.representation
    (eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ (twistObject χ w⁻¹ A.contragredient)) j' k)
    (eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ (twistObject χ w A))
      (sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A test w) k)

local notation "Φ[" j' "]" => reverseTestPairingIntegrand χ K ψ hψ ψ' hψ' A t z j'

private theorem reverse_testPairing_slice
    (j' : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj Ad)
    (hG : IsConnectedReductive G) (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (hj : HasIntegral h₁ hU₁ (radical ψ) Ad ν₀ f' Jvalue'[j']) (k : Γ) :
    Integrable (fun x : X₀ => ((R₀ k x).toReal : ℂ)) ν₀ ∧
      (∫ x : X₀, ((R₀ k x).toReal : ℂ) ∂ν₀) = Φ[j'] k := by
  let ℓ := twistEvaluationFunctional (A := A) (η').val.toMonoidHom hη' (eval₀ f k)
  have htest := hj k ℓ
  have he : (fun x : X₀ => ℓ.val (integrand h₁ hU₁ (radical ψ) Ad k f' x)) =
      fun x => ((R₀ k x).toReal : ℂ) := by
    funext x
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    change _ = ((normalizedTestAverage χ K hK t.subgroup ψ' ψ ((u : Γ) * k)).toReal : ℂ)
    exact (reverse_probe_mk h₀ hU₀ h₁ hU₁ (T := A)
      (ξ := (η).val.toMonoidHom) (ξ' := (η').val.toMonoidHom) (hξ := hη) (hξ' := hη') f f' k u).trans
      ((dualIntegrand_testSections_eq χ K ψ hψ ψ' hψ' A t z hK hG hδ ((u : Γ) * k)).trans
        (congrArg (fun a : ℝ≥0∞ => (a.toReal : ℂ))
          (normalizedTestAverage_swap χ K hK ψ hψ ψ' hψ' A t ((u : Γ) * k))))
  rw [he] at htest
  exact ⟨htest.1, htest.2⟩

/-- The inverse-parameter reverse-dual integral gives the same test value
on its own convergence domain. -/
theorem reverse_testPairing_eq
    (j' : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj Ad)
    (hG : IsConnectedReductive G) (hδ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (hψ'K : ∀ g : Γ, ∃ p : parabolic ψ', ∃ k : K, g = (p : Γ) * (k : Γ))
    (hj : HasIntegral h₁ hU₁ (radical ψ) Ad ν₀ f' Jvalue'[j']) :
    (∫ k in (K : Set Γ), Φ[j'] k ∂μG) = compactAdjunctionTestValue χ K hK ψ hψ ψ' hψ' A t := by
  have hcont : Continuous Φ[j'] :=
    (bilinearPairing_isLocallyConstant (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ Az)
      (leviInflatedInducingRepresentation h₀ hU₀ Ad) (smoothDualPairing A.representation) j' f).continuous
  have hi : Integrable Φ[j'] ((μG).restrict (K : Set Γ)) := hcont.continuousOn.integrableOn_compact hK
  have hf (k : Γ) (x : X₀) : R₀ k x ≠ ⊤ := by
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    change normalizedTestAverage χ K hK t.subgroup ψ' ψ ((u : Γ) * k) ≠ ⊤
    rw [← normalizedTestAverage_swap χ K hK ψ hψ ψ' hψ' A t]
    exact normalizedTestAverage_finite χ K hK ψ hψ ψ' hψ' A t hG ((u : Γ) * k)
  have hs := reverse_testPairing_slice χ K hK ψ hψ ψ' hψ' A t z j' hG hδ hj
  have he := integral_eq_of_iterated_lintegral ((μG).restrict (K : Set Γ)) ν₀ R₀ Φ[j'] hi hf hs
  rw [he, lintegral_normalizedQuotientTestAverage χ K hK t.subgroup ψ' ψ hψ hψK t.isCompact_subgroup,
    ← compactTestMass_swap χ K hK t.subgroup ψ ψ' hG hψ hψ' hψK hψ'K]
  rfl

end Reverse

end Langlands.Plancherel.ActualCommonLeviIwasawa
