import Langlands.BaseChange.SigmaOrbitRealTwist
import Langlands.BaseChange.RelativeNormRealTwist
import Langlands.BaseChange.SigmaLiftNormTwist
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.LocalField.SuppliedPadicExtension
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction

/-! # Restoring the original real twist of a supercuspidal σ-lift -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis CharZeroLocalField LocalField

universe u v uV uW

private theorem normTwistStabilizer_twist {F : Type u} [Field F] {E : Type v} [Field E]
    [Algebra F E] {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (χ : GeneralLinear n F →* ℂˣ) :
    normTwistStabilizer E (twist χ π) = normTwistStabilizer E π := by
  ext κ
  simp only [mem_normTwistStabilizer]
  apply and_congr_right'
  rw [twist_twist, mul_comm (κ.comp determinant), ← twist_twist]
  constructor
  · rintro ⟨e⟩
    have e' := twistEquiv χ⁻¹ e
    rw [twist_inv_twist, twist_inv_twist] at e'
    exact ⟨e'⟩
  · rintro ⟨e⟩
    exact ⟨twistEquiv χ e⟩

section LocalFields

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

private theorem realPowerCharacter_comp_norm [FiniteDimensional F E] (t : ℝ) :
    (realPowerCharacter (LocalFieldData.ofInstances F).normalizedAbsUnits t).comp
      (Units.map (Algebra.norm F : E →* F)) =
    realPowerCharacter (LocalFieldData.ofInstances E).normalizedAbsUnits t := by
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let T := topologicalData F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier L.Carrier := (inferInstance : FiniteDimensional F E)
  exact realPowerCharacter_comp_relativeNorm T S t

set_option maxHeartbeats 1300000 in
/-- Remove the common real twist from a lift of an exact orbit product. The
lower carrier and stabilizer are preserved, and the σ-lift uses the actual
untwisted upper product. -/
theorem exists_cuspidalSigmaLift_of_realPowerTwist
    (σ : E ≃ₐ[F] E) {l s n : ℕ} (hcyc : IsCyclicAlgebra σ l) (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P₁ : Representation ℂ (GeneralLinear n E) W) (t : ℝ) :
    letI := LocalFieldTopology.generalLinear_t2Space F (s * n)
    letI := LocalFieldTopology.generalLinear_locallyCompactSpace F (s * n)
    letI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (s * n)
    letI := LocalFieldTopology.generalLinear_t2Space E (s * n)
    letI := LocalFieldTopology.generalLinear_locallyCompactSpace E (s * n)
    letI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (s * n)
    let T := LocalFieldData.ofInstances F
    let S := LocalFieldData.ofInstances E
    let P := sigmaOrbitProduct σ s hn P₁
    let P' := sigmaOrbitProduct σ s hn (realPowerTwist (S.determinantNorm n) t P₁)
    ∀ (hP' : IsAdmissible P') (_hI' : P'.IsIrreducible)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (s * n) F) V)
      (hπ : IsAdmissible π) (A : SigmaIntertwiner σ (s * n) P') (c : ℂ),
      IsSupercuspidal π → π.IsIrreducible → Nat.card (normTwistStabilizer E π) = s →
      IsSigmaLift σ l π hπ P' hP' A c →
      let π₀ := realPowerTwist (T.determinantNorm (s * n)) (-t) π
      P.IsIrreducible ∧ IsSupercuspidal π₀ ∧ π₀.IsIrreducible ∧
        Nat.card (normTwistStabilizer E π₀) = s ∧
        ∃ (hπ₀ : IsAdmissible π₀) (hP : IsAdmissible P) (A₀ : SigmaIntertwiner σ (s * n) P),
          IsSigmaLift σ l π₀ hπ₀ P hP A₀ c := by
  dsimp only
  intro hP' hI' V _ _ π hπ A c hsc hi hcard hlift
  let : FiniteDimensional F E := hcyc.1
  let := LocalFieldTopology.generalLinear_t2Space F (s * n)
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F (s * n)
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (s * n)
  let := LocalFieldTopology.generalLinear_t2Space E (s * n)
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E (s * n)
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (s * n)
  let T := LocalFieldData.ofInstances F
  let S := LocalFieldData.ofInstances E
  let P := sigmaOrbitProduct σ s hn P₁
  let P' := sigmaOrbitProduct σ s hn (realPowerTwist (S.determinantNorm n) t P₁)
  let χ := realPowerCharacter T.normalizedAbsUnits (-t)
  let χ' := realPowerCharacter S.normalizedAbsUnits (-t)
  have hχ : IsOpen (χ.ker : Set Fˣ) := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    exact isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits _
  let ω : Quasicharacter F := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    exact { χ with continuous_toFun := CuspidalSupport.NormalHecke.continuous_of_isOpen_ker χ hχ }
  have hN : ω.toMonoidHom.comp (Units.map (Algebra.norm F : E →* F)) = χ' :=
    realPowerCharacter_comp_norm F E (-t)
  have h := sigmaLiftFieldTwist F E σ l (s * n) hcyc V _ π hπ P' hP' A c hlift ω
  rw [hN] at h
  obtain ⟨hπ₀, hP₀, A₀, _, hlift₀⟩ := h
  let e := sigmaOrbitProduct_realPowerTwistEquiv P₁ σ s hn t
  let e₀ := twistEquiv (χ'.comp determinant) e.symm
  have hCancel : realPowerTwist (S.determinantNorm (s * n)) (-t)
      (realPowerTwist (S.determinantNorm (s * n)) t P) = P := by
    rw [← realPowerTwist_add, neg_add_cancel, realPowerTwist_zero]
  have eP : (twist (χ'.comp determinant) P').Equiv P :=
    e₀.trans (equivOfRepresentationEq hCancel)
  have hP := (isAdmissible_iff_of_equiv eP).mp hP₀
  have hI := (isIrreducible_iff_of_equiv eP).mp ((isIrreducible_twist_iff _ _).mpr hI')
  let χF : GeneralLinear (s * n) F →* ℂˣ := χ.comp determinant
  have hχF : IsOpen (χF.ker : Set (GeneralLinear (s * n) F)) :=
    hχ.preimage (T.generalLinearDeterminant (s * n)).continuous
  have hs₀ : IsSupercuspidal (twist χF π) :=
    (isSupercuspidal_twist_iff _ hχF (ker_determinant_le_ker_comp χ) π).mpr hsc
  have hi₀ := (isIrreducible_twist_iff χF π).mpr hi
  have hc₀ : Nat.card (normTwistStabilizer E (twist χF π)) = s := by
    rw [normTwistStabilizer_twist, hcard]
  exact ⟨hI, hs₀, hi₀, hc₀, hπ₀, hP, A₀.transport eP,
    hlift₀.transport hπ₀ (Representation.Equiv.refl _) hP eP⟩

end LocalFields

end Langlands.BaseChange
