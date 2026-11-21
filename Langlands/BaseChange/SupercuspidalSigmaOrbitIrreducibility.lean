import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.BaseChange.SigmaOrbitProduct
import Langlands.LocalField.CanonicalTransport
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof

/-! # Irreducibility of a normalized sigma-orbit product of a supercuspidal -/

noncomputable section

set_option autoImplicit false

universe u v uW

namespace Langlands.BaseChange

open GeneralLinear
open scoped PadicField.CanonicalLocalField

section Padic

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{v} p)
  {K : Type u} [Field K] [Algebra (Padic p) K] [Algebra K E.Carrier]
  [IsScalarTower (Padic p) K E.Carrier] (σ : E.Carrier ≃ₐ[K] E.Carrier)

local notation "T" => E.canonicalTopologicalData

private theorem realPowerCharacter_entrywiseAut (n : ℕ) (t : ℝ) (i : ℕ)
    (g : GeneralLinear n E.Carrier) :
    realPowerCharacter (T).normalizedAbsUnits t (determinant (entrywiseAut (σ ^ i) n g)) =
      realPowerCharacter (T).normalizedAbsUnits t (determinant g) := by
  apply Units.ext
  simp only [coe_realPowerCharacter, (T).normalizedAbsUnits_coe]
  congr 2
  change (T).normalizedAbs ((σ ^ i).toRingHom.mapMatrix g.val).det = (T).normalizedAbs g.val.det
  rw [← RingHom.map_det]
  exact PadicField.CanonicalTransport.normalizedAbs_map E E ((σ ^ i).restrictScalars (Padic p)) _

set_option maxHeartbeats 1500000 in
private theorem sigmaOrbitProduct_irreducible_commonUniverse
    (d n : ℕ) (hn : 0 < n) {W : Type (max v uW)} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E.Carrier) W)
    (hI : P.IsIrreducible) (hS : IsSupercuspidal P) :
    Representation.IsIrreducible (sigmaOrbitProduct σ d hn P) := by
  let U := E.canonicalLocalFieldData
  let B := BlockShape.uniform d n hn
  obtain ⟨t, ht⟩ := supercuspidalRealUnitarization p E T n hn W P hI hS
  let χ : Induction.SmoothCharacter ℂ E.Carrierˣ :=
    ⟨realPowerCharacter (T).normalizedAbsUnits t,
      isOpen_ker_realPowerCharacter _ (T).isOpen_ker_normalizedAbsUnits _⟩
  let η : GeneralLinear n E.Carrier →* ℂˣ := χ.toMonoidHom.comp determinant
  let P' := twist η P
  have hu : IsUnitarizable P' := ht
  have hη : IsOpen (η.ker : Set (GeneralLinear n E.Carrier)) :=
    isOpen_ker_realPowerCharacter ((T).determinantNorm n) ((T).isOpen_ker_determinantNorm n) t
  have hP' := (isIrreducible_twist_iff η P).mpr hI
  have hP's := (isSmooth_twist_iff η P hη).mpr hS.1.1
  have hσ : Continuous σ :=
    IsModuleTopology.continuous_of_linearMap (σ.restrictScalars (Padic p)).toLinearMap
  have hprod : Representation.IsIrreducible (sigmaOrbitProduct σ d hn P') :=
    (sigmaOrbitProduct_irreducible_unitarizable.{u, v, uW} p E K T σ d n hn W P' hP' hu hσ hP's).1
  let R (i : Fin B.length) := P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom
  have hfactor (i : Fin B.length) : P'.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom =
      twist η (R i) := by
    ext g x
    change (χ.toMonoidHom (determinant (entrywiseAut (σ ^ (i : ℕ)) n g)) : ℂ) •
        P (entrywiseAut (σ ^ (i : ℕ)) n g) x =
      (χ.toMonoidHom (determinant g) : ℂ) • P (entrywiseAut (σ ^ (i : ℕ)) n g) x
    rw [show χ.toMonoidHom = realPowerCharacter (T).normalizedAbsUnits t from rfl,
      realPowerCharacter_entrywiseAut E σ n t _ g]
  have hB : (fun i : Fin B.length => P'.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom) =
      fun i => twist η (R i) := funext hfactor
  let e := U.normalizedProductDeterminantTwistEquiv B χ R
  have hunit : Representation.IsIrreducible
      (U.normalizedProductInduced B (fun i => twist η (R i))) := by
    have hEq := congrArg (fun S : ∀ i : Fin B.length,
        Representation ℂ (GeneralLinear (B.size i) E.Carrier) W =>
      (U.normalizedProductInduced B S).IsIrreducible) hB
    exact hEq.mp hprod
  exact (isIrreducible_twist_iff (χ.toMonoidHom.comp determinant) _).mp
    ((isIrreducible_iff_of_equiv e).mpr hunit)

/-- Every actual normalized orbit induction of an irreducible supercuspidal
is irreducible. All block carriers retain their original universe. -/
def SupercuspidalSigmaOrbitIrreducibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : PadicField.{v} p)
    (K : Type u) [Field K] [Algebra (Padic p) K] [Algebra K E.Carrier]
    [IsScalarTower (Padic p) K E.Carrier] (σ : E.Carrier ≃ₐ[K] E.Carrier)
    (d n : ℕ) (hn : 0 < n) (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E.Carrier) W),
    P.IsIrreducible → IsSupercuspidal P → Representation.IsIrreducible (sigmaOrbitProduct σ d hn P)

set_option maxHeartbeats 1000000 in
/-- Unitarize the orbit blocks by one common real determinant twist and
use irreducibility of the entire unitary normalized product. -/
theorem supercuspidalSigmaOrbitIrreducibility : SupercuspidalSigmaOrbitIrreducibilityStatement.{u, v, uW} := by
  intro p _ E K _ _ _ _ σ d n hn W _ _ P hI hS
  let P' := universeLiftRepresentation.{v} P
  let e := universeLiftEquiv.{v} P
  have hP' := sigmaOrbitProduct_irreducible_commonUniverse.{u, v, uW} E σ d n hn P'
    ((isIrreducible_iff_of_equiv e).mp hI) (isSupercuspidal_of_equiv e hS)
  let B := BlockShape.uniform d n hn
  let eprod := E.canonicalLocalFieldData.normalizedProductInducedEquiv B
    (fun i => BinaryTensor.compEquiv e (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom)
  exact (isIrreducible_iff_of_equiv eprod).mpr hP'

end Padic

end Langlands.BaseChange
