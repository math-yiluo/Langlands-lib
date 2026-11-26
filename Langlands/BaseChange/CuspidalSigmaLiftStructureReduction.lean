import Langlands.BaseChange.CuspidalSigmaLiftStructureRankOne
import Langlands.BaseChange.CuspidalSigmaLiftStructureStatement
import Langlands.BaseChange.DiscreteSeriesSigmaLiftStatement
import Langlands.BaseChange.NormTrivialCharacterGroup
import Langlands.BaseChange.SigmaDiscreteSeriesOrbitDecompositionStatement
import Langlands.BaseChange.SigmaLiftNormTwist
import Langlands.BaseChange.SigmaLiftUniquenessStatement
import Langlands.BaseChange.SigmaOrbitDeterminantTwist
import Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison
import Langlands.LocalField.SuppliedPadicExtension
import Langlands.Representation.Classification.SupercuspidalTwist

/-! # Reduction of the supercuspidal σ-lift structure to unitary data -/

noncomputable section

namespace Langlands.BaseChange

open CharZeroLocalField GeneralLinear HarmonicAnalysis JacquetLanglands LocalClassField LocalField

universe u v uV uW

/-- Identifying the discrete orbit block of a lift from a unitarily normalized
supercuspidal. The local self-pair Euler comparison is used at this step. -/
def DiscreteSigmaLiftOrbitIdentificationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l → 0 < n →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π),
      π.IsIrreducible → IsSupercuspidal π → IsSquareIntegrable π →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear n E) W) (hP : IsAdmissible P),
      IsSigmaDiscreteSeries σ n P →
    ∀ (A : SigmaIntertwiner σ n P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
       haveI := LocalFieldTopology.generalLinear_t2Space E n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ (t m : ℕ) (hm : 0 < m) (h : t * m = n)
      {X : Type uW} [AddCommGroup X] [Module ℂ X]
      (Q : Representation ℂ (GeneralLinear m E) X),
      Q.IsIrreducible → IsSquareIntegrable Q →
      (∀ i : ℕ, Nonempty (Q.Equiv (Q.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i) →
      Nonempty (P.Equiv ((sigmaOrbitProduct σ t hm Q).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
      IsSupercuspidal Q ∧ t = Nat.card (normTwistStabilizer E π)

private theorem nonempty_twistEquiv_iff {G : Type*} [Group G]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (χ : G →* ℂˣ) :
    Nonempty ((twist χ ρ).Equiv (twist χ τ)) ↔ Nonempty (ρ.Equiv τ) := by
  constructor
  · rintro ⟨e⟩
    have e' := twistEquiv χ⁻¹ e
    rw [twist_inv_twist, twist_inv_twist] at e'
    exact ⟨e'⟩
  · rintro ⟨e⟩
    exact ⟨twistEquiv χ e⟩

private theorem normTwistStabilizer_twist {F : Type u} [Field F] {E : Type v}
    [Field E] [Algebra F E] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (χ : GeneralLinear n F →* ℂˣ) :
    normTwistStabilizer E (twist χ π) = normTwistStabilizer E π := by
  ext κ
  rw [mem_normTwistStabilizer, mem_normTwistStabilizer]
  have hcomm : twist (κ.comp determinant) (twist χ π) = twist χ (twist (κ.comp determinant) π) := by
    rw [twist_twist, twist_twist]
    exact congrArg (fun ξ => twist ξ π) (mul_comm (κ.comp determinant) χ)
  rw [hcomm, nonempty_twistEquiv_iff]

private theorem nonempty_comp_equiv_detTwist_iff {F : Type u} [Field F] {E : Type v}
    [Field E] [Algebra F E] {m : ℕ} {X : Type uW} [AddCommGroup X] [Module ℂ X]
    (Q : Representation ℂ (GeneralLinear m E) X) (γ : E ≃ₐ[F] E) (χ : Eˣ →* ℂˣ)
    (hχ : ∀ x : Eˣ, χ (Units.map γ.toRingHom.toMonoidHom x) = χ x) :
    Nonempty ((twist (χ.comp determinant) Q).Equiv
      ((twist (χ.comp determinant) Q).comp (entrywiseAut γ m).toMonoidHom)) ↔
    Nonempty (Q.Equiv (Q.comp (entrywiseAut γ m).toMonoidHom)) := by
  rw [twist_comp]
  have h : (χ.comp (determinant (n := m))).comp (entrywiseAut γ m).toMonoidHom =
      χ.comp determinant := by
    ext g : 1
    change χ (determinant (Matrix.GeneralLinearGroup.map γ.toRingHom g)) = χ (determinant g)
    rw [Matrix.GeneralLinearGroup.map_det]
    exact hχ (determinant g)
  rw [h, nonempty_twistEquiv_iff]

private theorem determinantCharacter_isOpen_ker {E : Type v} [Field E]
    [TopologicalSpace E] [IsTopologicalRing E] (χ : Induction.SmoothCharacter ℂ Eˣ) (n : ℕ) :
    IsOpen (((χ.toMonoidHom.comp (determinant (n := n))).ker) : Set (GeneralLinear n E)) :=
  IsOpen.preimage determinantContinuous.continuous χ.isOpen_ker

private theorem continuous_normUnits_of_localField
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [FiniteDimensional F E] [IsModuleTopology F E] :
    Continuous (Units.map (Algebra.norm F : E →* F)) := by
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let K := padicField F
  let L := PadicField.ofField (p := p) E
  let T := topologicalData F
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : TopologicalSpace L.Carrier := S.topology
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F E)
  exact (localNorm T S).continuous

set_option maxHeartbeats 4000000 in
/-- Normalize the lower supercuspidal by a determinant twist. Construct a
σ-discrete lift, identify its orbit block, and transfer the result back to the
given lift using uniqueness and the inverse norm determinant twist. -/
theorem cuspidalSigmaLiftStructure_of_normalized
    (hExists : DiscreteSeriesSigmaLiftStatement.{u, v, uV, uW})
    (hUnique : SigmaLiftUniquenessStatement.{u, v, uV, uW, uW})
    (hOrbit : SigmaDiscreteSeriesOrbitDecompositionStatement.{u, v, uW})
    (hIdentify : DiscreteSigmaLiftOrbitIdentificationStatement.{u, v, uV, uW}) :
    CuspidalSigmaLiftStructureStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l n hcyc hn V _ _ π hπ hπs hπi
    W _ _ P hP hPi A c hlift
  by_cases hrank : n = 1
  · subst n
    exact cuspidalSigmaLiftStructure_rankOne F E σ l π hπ hπi P hP hPi A
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : FiniteDimensional F E := hcyc.1
  let K := padicField F
  let T := topologicalData F
  obtain ⟨s, hs⟩ := padicSupercuspidalEssentialSquareIntegrability p K T n hn V π hπi hπs
  let α := realPowerCharacter (Plancherel.fieldNormUnits F) (-s)
  have hα : IsLocallyConstant α :=
    (Plancherel.fieldNormUnits_isLocallyConstant F).comp
      (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom (-s))))
  let ω : Quasicharacter F := ⟨α, hα.continuous⟩
  let N := Units.map (Algebra.norm F : E →* F)
  let β := ω.toMonoidHom.comp N
  have hN : Continuous N := continuous_normUnits_of_localField
  have hβ : IsLocallyConstant β := hα.comp_continuous hN
  let χ : Induction.SmoothCharacter ℂ Eˣ := ⟨β⁻¹, (hβ.comp Inv.inv).isOpen_fiber 1⟩
  have hχ (j : ℕ) (x : Eˣ) :
      χ.toMonoidHom (Units.map (σ ^ j).toRingHom.toMonoidHom x) = χ.toMonoidHom x := by
    apply congrArg (fun y => (ω y)⁻¹)
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv (σ ^ j) (x : E)
  let π₀ := twist (α.comp determinant) π
  change IsSquareIntegrable π₀ at hs
  have hπ₀i : π₀.IsIrreducible := (isIrreducible_twist_iff _ π).mpr hπi
  have hπ₀s : IsSupercuspidal π₀ :=
    (isSupercuspidal_twist_iff _
      (determinantCharacter_isOpen_ker ⟨α, hα.isOpen_fiber 1⟩ n)
      (ker_determinant_le_ker_comp α) π).mpr hπs
  let P₀ := twist (β.comp determinant) P
  have hP₀i : P₀.IsIrreducible := (isIrreducible_twist_iff _ P).mpr hPi
  obtain ⟨hπ₀, hP₀, A₀, -, hlift₀⟩ :=
    sigmaLiftFieldTwist F E σ l n hcyc V W π hπ P hP A c hlift ω
  obtain ⟨Y, _, _, R, hR, AR, cR, hRi, hLiftR, hRd⟩ :=
    hExists F E σ l n hcyc π₀ hπ₀ hπ₀i hs.isEssentiallySquareIntegrable
  have hRdis := hRd hs
  obtain ⟨t, m, hm, h, X, _, _, Q, hQi, hQsq, hperiod, hRorbit⟩ :=
    hOrbit F E σ l n hcyc hn Y R hRdis
  obtain ⟨hQs, ht⟩ := hIdentify F E σ l n hcyc hn π₀ hπ₀ hπ₀i hπ₀s hs
    R hR hRdis AR cR hLiftR t m hm h Q hQi hQsq hperiod hRorbit
  change t = Nat.card (normTwistStabilizer E (twist (α.comp determinant) π)) at ht
  rw [normTwistStabilizer_twist] at ht
  obtain ⟨e⟩ := hUnique F E σ l n hcyc π₀ hπ₀ hπ₀i P₀ hP₀ hP₀i R hR hRi A₀ AR c cR hlift₀ hLiftR
  obtain ⟨eOrbit⟩ := hRorbit
  obtain ⟨eu⟩ := sigmaOrbitDeterminantTwist F E σ χ hχ t m n hm h X W Q P₀ ⟨e.trans eOrbit⟩
  have hcancel : twist (χ.toMonoidHom.comp (determinant (n := n))) P₀ = P := by
    change twist ((β⁻¹).comp determinant) (twist (β.comp determinant) P) = P
    rw [MonoidHom.inv_comp, twist_inv_twist]
  rw [hcancel] at eu
  let Q' := twist (χ.toMonoidHom.comp determinant) Q
  have hQ's : IsSupercuspidal Q' :=
    (isSupercuspidal_twist_iff _ (determinantCharacter_isOpen_ker χ m)
      (ker_determinant_le_ker_comp χ.toMonoidHom) Q).mpr hQs
  have hQ'i : Q'.IsIrreducible := (isIrreducible_twist_iff _ Q).mpr hQi
  have hQ'period (i : ℕ) :
      Nonempty (Q'.Equiv (Q'.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i :=
    (nonempty_comp_equiv_detTwist_iff Q (σ ^ i) χ.toMonoidHom (hχ i)).trans (hperiod i)
  refine ⟨normTwistStabilizer_card_dvd hcyc π, ?_⟩
  subst t
  exact ⟨m, hm, h, X, inferInstance, inferInstance, Q', hQ's, hQ'i, hQ'period, ⟨eu⟩⟩

end Langlands.BaseChange
