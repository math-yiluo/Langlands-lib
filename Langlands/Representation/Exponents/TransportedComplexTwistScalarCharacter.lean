import Langlands.Representation.Twist.LeviComplexPowerConjugationProof
import Langlands.Representation.Unitary.CentralCharacterProof
import Langlands.Representation.MatrixCoefficient.GroupTransport
import Langlands.Representation.Classification.ProductLeviCentralCharacter

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear CuspidalSupport

universe uF uV

/-- The transported complex twist has a block-scalar character with
open kernel and the size-weighted negative real exponent. -/
theorem transportedComplexTwistScalarCharacter
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (C E : BlockShape n)
    (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F.Carrier) C E w)
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier))
    (hi : Representation.IsIrreducible ω.ρ)
    (ha : letI := T.topology; IsAdmissible ω.ρ)
    (hu : IsUnitarizable ω.ρ) (v b : Fin C.length → ℝ) :
    letI := T.topology
    ∃ χ : (Fin E.length → F.Carrierˣ) →* ℂˣ,
      IsOpen (χ.ker : Set (Fin E.length → F.Carrierˣ)) ∧
      Classification.HasScalarCharacter
        (transport C E w hw (T.leviComplexPowerTwist C
          (fun k => -(v k : ℂ) + Complex.I * (b k : ℂ)) ω.ρ))
        (E.blockScalarLevi F.Carrier) χ ∧
      T.IsRealPartOf χ
        (fun j => -((E.size j : ℝ) * v ((blockEquiv hw).symm j))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup C
  let := T.leviTopologicalGroup E
  have := hi
  have : Nontrivial ω := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (C.Levi F.Carrier)) ω.ρ.asModule
  obtain ⟨c⟩ := unitarizableCentralCharacter ω.ρ ha hi hu
  let e : E.Levi F.Carrier ≃ₜ* C.Levi F.Carrier :=
    { toMulEquiv := (leviConjugation C E w hw).symm
      continuous_toFun := continuous_leviConjugation_symm C E w hw
      continuous_invFun := continuous_leviConjugation C E w hw }
  let cE : UnitaryCentralCharacter (transport C E w hw ω.ρ) :=
    c.compContinuousMulEquiv e
  let z : Fin E.length → ℂ := fun j =>
    -(v ((blockEquiv hw).symm j) : ℂ) +
      Complex.I * (b ((blockEquiv hw).symm j) : ℂ)
  let ψ : (Fin E.length → F.Carrierˣ) →* ℂˣ :=
    cE.character.comp (E.blockScalarToCenter F.Carrier)
  let θ : (Fin E.length → F.Carrierˣ) →* ℂˣ :=
    (T.leviComplexPowerCharacter E z).comp (E.blockScalarLevi F.Carrier)
  let χ := ψ * θ
  have hscalar : Classification.HasScalarCharacter
      (transport C E w hw (T.leviComplexPowerTwist C
        (fun k => -(v k : ℂ) + Complex.I * (b k : ℂ)) ω.ρ))
      (E.blockScalarLevi F.Carrier) χ := by
    rw [T.transport_leviComplexPowerTwist C E w hw]
    intro a x
    change (T.leviComplexPowerCharacter E z (E.blockScalarLevi F.Carrier a) : ℂ) •
      transport C E w hw ω.ρ (E.blockScalarLevi F.Carrier a) x = (χ a : ℂ) • x
    rw [show transport C E w hw ω.ρ (E.blockScalarLevi F.Carrier a) x =
      (cE.character (E.blockScalarToCenter F.Carrier a) : ℂ) • x from
        cE.acts (E.blockScalarToCenter F.Carrier a) x]
    simp only [χ, ψ, θ, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul,
      smul_smul]
    rw [mul_comm]
  have hcont : Continuous (E.blockScalarLevi F.Carrier) := by
    change Continuous fun a : Fin E.length → F.Carrierˣ =>
      fun j => GeneralLinear.scalar (n := E.size j) (a j)
    exact continuous_pi fun j =>
      GeneralLinear.scalarContinuous.continuous.comp (continuous_apply j)
  have hsmooth : IsSmooth (transport C E w hw
      (T.leviComplexPowerTwist C
        (fun k => -(v k : ℂ) + Complex.I * (b k : ℂ)) ω.ρ)) :=
    isSmooth_transport C E w hw
      ((T.isSmooth_leviComplexPowerTwist_iff C _ ω.ρ).mpr ha.1)
  refine ⟨χ, hscalar.isOpen_ker hcont hsmooth, hscalar, ?_⟩
  intro a
  change ‖(ψ a : ℂ) * (θ a : ℂ)‖ = _
  rw [norm_mul, show ‖(ψ a : ℂ)‖ = 1 from
    cE.norm_eq_one (E.blockScalarToCenter F.Carrier a), one_mul]
  change ‖(T.leviComplexPowerCharacter E z (E.blockScalarLevi F.Carrier a) : ℂ)‖ = _
  rw [T.coe_leviComplexPowerCharacter_blockScalar E, norm_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos
    (T.normalizedAbs_pos (a j).ne_zero)]
  congr 1
  simp [z, Complex.mul_re]

end Langlands
