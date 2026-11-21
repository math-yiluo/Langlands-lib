import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Determinant norm twists of sigma-lifts over cyclic fields -/

noncomputable section

open scoped BigOperators

namespace Langlands.BaseChange

open HarmonicAnalysis GeneralLinear MeasureTheory TraceFormula QuotientIntegration

universe u v uV uW

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Norm

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n l : ℕ}

/-- The determinant of the norm-associated base matrix is the actual norm
of the determinant upstairs. -/
theorem IsNormAssociated.determinant_eq_fieldNorm (hcyc : IsCyclicAlgebra σ l)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (h : IsNormAssociated σ l δ γ) :
    Units.map (Algebra.norm F : E →* F) (determinant δ) = determinant γ :=
  Units.ext (h.norm_determinant_eq hcyc)

private theorem fieldNorm_determinant_entrywiseAut (g : GeneralLinear n E) :
    Units.map (Algebra.norm F : E →* F) (determinant (entrywiseAut σ n g)) =
      Units.map (Algebra.norm F : E →* F) (determinant g) := by
  change Units.map (Algebra.norm F : E →* F)
    (determinant (Matrix.GeneralLinearGroup.map σ.toRingHom g)) = _
  rw [Matrix.GeneralLinearGroup.map_det]
  exact Units.ext (Algebra.norm_eq_of_algEquiv σ (determinant g : E))

end Norm

section TestFunctions

variable {G : Type*} [Group G] [TopologicalSpace G]

private def characterWeightedTest (χ : G →* ℂˣ)
    (hχ : IsLocallyConstant fun g : G => (χ g : ℂ)) (f : SchwartzBruhat G) :
    SchwartzBruhat G :=
  ⟨fun g => (χ g : ℂ) * f g, hχ.comp₂ f.locallyConstant (· * ·), f.hasCompactSupport.mul_left⟩

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem twistedDistribution_twist_characterWeightedTest (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (χ : G →* ℂˣ)
    (hχ : IsLocallyConstant fun g : G => (χ g : ℂ))
    (htw : IsAdmissible (twist χ ρ)) (A : Module.End ℂ V) (f : SchwartzBruhat G) :
    twistedDistribution μ (twist χ ρ) htw A f =
      twistedDistribution μ ρ hρ A (characterWeightedTest χ hχ f) := by
  rw [twistedDistribution_apply, twistedDistribution_apply]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  simp only [Character.finiteRankIntegratedAction_coe]
  congr 1
  ext x
  rw [Hecke.integratedAction_apply, Hecke.integratedAction_apply]
  congr 1
  ext g
  simp only [Hecke.actionIntegrand_apply]
  change f g • ((χ g : ℂ) • ρ g x) = ((χ g : ℂ) * f g) • ρ g x
  rw [smul_smul, mul_comm (f g) (χ g : ℂ)]

end TestFunctions

section WeightedOrbits

private theorem twistedOrbitalIntegral_mul_character {G : Type*} [Group G] [TopologicalSpace G]
    {A : Type*} [FunLike A G G] [MonoidHomClass A G G]
    (θ : A) (δ : G) (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (χ : G →* ℂˣ) (hχ : ∀ g, χ (θ g) = χ g) (φ : G → ℂ) :
    twistedOrbitalIntegral θ δ ν (fun x => (χ x : ℂ) * φ x) =
      (χ δ : ℂ) * twistedOrbitalIntegral θ δ ν φ := by
  unfold twistedOrbitalIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun q => ?_
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [twistedOrbitFunction_mk, map_mul, map_inv, hχ]
    have h : (χ x)⁻¹ * χ δ * χ x = χ δ := by
      rw [mul_comm (χ x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [h]

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  [TopologicalSpace F] [IsTopologicalRing F] [TopologicalSpace E] [IsTopologicalRing E]
  {σ : E ≃ₐ[F] E} {n l : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- Multiplying concordant functions by characters matched on norm pairs
preserves concordance when the upper character is twist-invariant. -/
theorem AreConcordant.mul_characters
    {μF : Measure (GeneralLinear n F)} {μE : Measure (GeneralLinear n E)}
    {φ : GeneralLinear n E → ℂ} {f : GeneralLinear n F → ℂ}
    (h : AreConcordant σ l μF μE φ f)
    (χF : GeneralLinear n F →* ℂˣ) (χE : GeneralLinear n E →* ℂˣ)
    (hE : ∀ g, χE (entrywiseAut σ n g) = χE g)
    (hN : ∀ δ γ, IsNormAssociated σ l δ γ → χE δ = χF γ) :
    AreConcordant σ l μF μE (fun x => (χE x : ℂ) * φ x) (fun x => (χF x : ℂ) * f x) := by
  constructor
  · intro γ hreg hoff μγ _ _ νγ hνγ
    change twistedOrbitalIntegral (MonoidHom.id _) γ νγ (fun x => (χF x : ℂ) * f x) = 0
    rw [twistedOrbitalIntegral_mul_character _ _ _ χF (fun _ => rfl), ← orbitalIntegral,
      h.1 γ hreg hoff μγ νγ hνγ, mul_zero]
  · intro δ γ ha hreg μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have heq := h.2 δ γ ha hreg μδ μγ νδ νγ hνδ hνγ hμ
    unfold sigmaOrbitalIntegral orbitalIntegral at heq ⊢
    rw [twistedOrbitalIntegral_mul_character (entrywiseAut σ n) δ νδ χE hE,
      twistedOrbitalIntegral_mul_character (MonoidHom.id _) γ νγ χF (fun _ => rfl),
      hN δ γ ha, heq]

end WeightedOrbits

section Twisting

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

private theorem nonarchimedeanGroup_of_locallyProfinite : NonarchimedeanGroup G := by
  refine ⟨fun U hU => ?_⟩
  obtain ⟨J, -, hJ⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
  exact ⟨J, hJ⟩

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] [FiniteDimensional F E] {n : ℕ}

omit [IsTopologicalRing E] in
private theorem continuous_fieldNorm : Continuous (Algebra.norm F : E → F) := by
  let b := Module.finBasis F E
  have h : Continuous (fun x : E => (Algebra.leftMulMatrix b x).det) :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det
  convert h using 1
  ext x
  exact Algebra.norm_eq_matrix_det b x

end Twisting

/-- Corresponding determinant characters preserve the distributional
sigma-lift relation over a cyclic field extension. -/
def SigmaLiftFieldTwistStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hcyc : IsCyclicAlgebra σ l),
    letI : Module.Finite F E := hcyc.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (P : Representation ℂ (GeneralLinear n E) W) (hP : IsAdmissible P)
      (A : SigmaIntertwiner σ n P) (c : ℂ),
      IsSigmaLift σ l π hπ P hP A c →
      ∀ (ω : Quasicharacter F),
        let πω := twist (ω.toMonoidHom.comp determinant) π
        let Pω := twist ((ω.toMonoidHom.comp (Units.map (Algebra.norm F : E →* F))).comp determinant) P
        ∃ (hπω : IsAdmissible πω) (hPω : IsAdmissible Pω) (Aω : SigmaIntertwiner σ n Pω),
          Aω.toLinearMap = A.toLinearMap ∧ IsSigmaLift σ l πω hπω Pω hPω Aω c

theorem sigmaLiftFieldTwist : SigmaLiftFieldTwistStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hcyc
  let : Module.Finite F E := hcyc.1
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ P hP A c hlift ω
  let χF := ω.toMonoidHom.comp (determinant (n := n))
  let χE := (ω.toMonoidHom.comp (Units.map (Algebra.norm F : E →* F))).comp (determinant (n := n))
  have hcF : Continuous χF := ω.continuous.comp determinantContinuous.continuous
  have hcN : Continuous (Units.map (Algebra.norm F : E →* F)) :=
    (continuous_fieldNorm (F := F) (E := E)).units_map _
  have hcE : Continuous χE := ω.continuous.comp (hcN.comp determinantContinuous.continuous)
  let : NonarchimedeanGroup (GeneralLinear n F) := nonarchimedeanGroup_of_locallyProfinite
  let : NonarchimedeanGroup (GeneralLinear n E) := nonarchimedeanGroup_of_locallyProfinite
  have hlocF := RankinSelberg.isLocallyConstant_of_continuous_complex_character χF hcF
  have hlocE := RankinSelberg.isLocallyConstant_of_continuous_complex_character χE hcE
  have hπω : IsAdmissible (twist χF π) :=
    (isAdmissible_twist_iff χF π (isOpen_ker_of_continuous_complex_character χF hcF)).mpr hπ
  have hPω : IsAdmissible (twist χE P) :=
    (isAdmissible_twist_iff χE P (isOpen_ker_of_continuous_complex_character χE hcE)).mpr hP
  have hE (g : GeneralLinear n E) : χE (entrywiseAut σ n g) = χE g :=
    congrArg ω (fieldNorm_determinant_entrywiseAut (σ := σ) g)
  have hN (δ : GeneralLinear n E) (γ : GeneralLinear n F) (ha : IsNormAssociated σ l δ γ) :
      χE δ = χF γ := congrArg ω (ha.determinant_eq_fieldNorm hcyc)
  let Aω : SigmaIntertwiner σ n (twist χE P) :=
    Representation.Equiv.mk A.toLinearEquiv fun g => LinearMap.ext fun x => by
      change A.toLinearEquiv ((χE g : ℂ) • P g x) =
        (χE (entrywiseAut σ n g) : ℂ) • P (entrywiseAut σ n g) (A.toLinearEquiv x)
      rw [map_smul, hE]
      exact congrArg (fun y : W => (χE g : ℂ) • y) (LinearMap.congr_fun (A.comp_apply_eq g) x)
  refine ⟨hπω, hPω, Aω, rfl, hlift.1, ?_⟩
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μF _ μE _ φ f h
  change twistedDistribution μE (twist χE P) hPω A.toLinearMap φ =
    c * Character.distribution μF (twist χF π) hπω f
  rw [twistedDistribution_twist_characterWeightedTest μE P hP χE hlocE hPω,
    ← twistedDistribution_one μF (twist χF π) hπω,
    twistedDistribution_twist_characterWeightedTest μF π hπ χF hlocF hπω, twistedDistribution_one]
  exact hlift.2 μF μE _ _ (h.mul_characters χF χE hE hN)

end Langlands.BaseChange
