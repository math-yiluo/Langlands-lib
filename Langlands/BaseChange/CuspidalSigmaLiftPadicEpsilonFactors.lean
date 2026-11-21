import Langlands.BaseChange.NormTwistFibreReduction
import Langlands.BaseChange.SigmaOrbitBlockFactors
import Langlands.BaseChange.SigmaOrbitSeparatedEpsilonProduct
import Langlands.BaseChange.SupercuspidalEpsilonConductorOfPadicData
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.Representation.Twist.SubquotientProof

/-! # Local epsilon and conductor certificates on supplied p-adic fields -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis

universe u v uV uW

/-- Individual standard epsilon conductor certificates for the norm-trivial
base twists and the extension orbit blocks, and the actual epsilon product for
the representation equivalent to that orbit. -/
def CuspidalSigmaLiftPadicEpsilonFactorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := S.topology
    letI := S.valuativeRel
    letI := S.localField
    ∀ [IsModuleTopology F.Carrier E.Carrier]
      (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (k s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V),
    π.IsIrreducible → GeneralLinear.IsSupercuspidal π →
    ∀ {W₁ : Type uW} [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E.Carrier) W₁),
    P₁.IsIrreducible → GeneralLinear.IsSupercuspidal P₁ →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E.Carrier) W),
    Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
      (GeneralLinear.reindex (R := E.Carrier) (finCongr h)).symm.toMonoidHom)) →
    ∀ (X : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ ∈ X, IsNormTrivial E.Carrier κ) →
    ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (ψE : UnitaryAdditiveCharacter E.Carrier)
      (νF : LocalFactor.PadicAbelian.SelfDualHaar T ψF)
      (νE : LocalFactor.PadicAbelian.SelfDualHaar S ψE),
    ∃ (aF : (F.Carrierˣ →* ℂˣ) → ℕ) (aOrbit : Fin s → ℕ)
      (eF : (F.Carrierˣ →* ℂˣ) → ℂˣ × ℤ) (eOrbit : Fin s → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
      (∀ κ ∈ X, IsStandardEpsilonConductor ψF νF.val
        (twist (κ.comp GeneralLinear.determinant) π) (aF κ) (eF κ)) ∧
      (∀ i : Fin s, IsStandardEpsilonConductor ψE νE.val
        (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) (aOrbit i) (eOrbit i)) ∧
      OrbitProductEpsilonMultiplicativity ψE νE.val P eOrbit eP

set_option maxHeartbeats 600000 in
/-- Assemble the two local families of certificates, with no base-change
comparison across the fields. -/
theorem cuspidalSigmaLiftPadicEpsilonFactors :
    CuspidalSigmaLiftPadicEpsilonFactorsStatement.{u, v, uV, uW} := by
  classical
  intro p _ F E _ _ T S _ σ k s k₁ hr V _ _ π hi hs W₁ _ _ P₁ hi₁ hs₁ W _ _ P horbit X hX ψF ψE νF νE
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let : FiniteDimensional F.Carrier E.Carrier := FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have hsuper (κ : F.Carrierˣ →* ℂˣ) (hκ : IsNormTrivial E.Carrier κ) :
      GeneralLinear.IsSupercuspidal (twist (κ.comp GeneralLinear.determinant) π) := by
    let : NontriviallyNormedField F.Carrier := LocalGalois.localNormedField F.Carrier
    let : CompleteSpace F.Carrier := LocalGalois.localNormedField_complete F.Carrier
    exact (hκ.isSupercuspidal_twist_iff π).mpr hs
  have hex (κ : F.Carrierˣ →* ℂˣ) : ∃ (a : ℕ) (e : ℂˣ × ℤ), κ ∈ X →
      IsStandardEpsilonConductor ψF νF.val (twist (κ.comp GeneralLinear.determinant) π) a e := by
    by_cases hκ : κ ∈ X
    · obtain ⟨a, e, he⟩ := supercuspidalEpsilonConductorOfPadicData p F T ψF νF
        (twist (κ.comp GeneralLinear.determinant) π) ((isIrreducible_twist_iff _ π).mpr hi)
        (hsuper κ (hX κ hκ))
      exact ⟨a, e, fun _ => he⟩
    · exact ⟨0, (1, 0), fun h => False.elim (hκ h)⟩
  choose aF eF hF using hex
  obtain ⟨hb, L, LD, hL, hLD, hsep⟩ := sigmaOrbitBlockFactors p F.Carrier E S σ s k₁ ψE νE P₁ hi₁ hs₁
  have he (i : Fin s) := supercuspidalEpsilonConductorOfPadicData p E S ψE νE
    (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) (hb i).1 (hb i).2.1
  choose aOrbit eOrbit hOrbit using he
  let νE' : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E.Carrier) ψE :=
    ⟨νE.val, νE.property⟩
  have hprod := sigmaOrbitSeparatedEpsilonProduct F.Carrier E.Carrier σ s k₁ k hr P₁ P horbit
    ψE νE' eOrbit L LD (fun i => (hb i).2.2) (fun i => (hOrbit i).1) hL hLD hsep
  exact ⟨aF, aOrbit, eF, eOrbit, _, hF, hOrbit, hprod⟩

end Langlands.BaseChange
