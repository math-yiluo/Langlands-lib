import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.AllField.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Twist.PullbackProof
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof

/-! # A common real determinant twist of the supercuspidal σ-orbit -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe u v uW

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]

private theorem realPowerDet_comp_entrywiseAut (σ : E ≃ₐ[F] E) (t : ℝ) (n : ℕ) :
    (realPowerCharacter ((LocalFieldData.ofInstances E).determinantNorm n) t).comp
      (entrywiseAut σ n).toMonoidHom =
        realPowerCharacter ((LocalFieldData.ofInstances E).determinantNorm n) t := by
  let T := LocalFieldData.ofInstances E
  ext g : 1
  change realPowerCharacter (T.determinantNorm n) t (entrywiseAut σ n g) =
    realPowerCharacter (T.determinantNorm n) t g
  unfold realPowerCharacter
  simp only [MonoidHom.comp_apply]
  rw [show T.determinantNorm n (entrywiseAut σ n g) = T.determinantNorm n g from
    determinantNorm_entrywiseAut σ n g]

variable {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (P : Representation ℂ (GeneralLinear n E) W) (σ : E ≃ₐ[F] E)

/-- A common real twist does not change any Galois equivalence test. -/
theorem nonempty_equiv_conjugate_realPowerTwist_iff (t : ℝ) :
    let T := LocalFieldData.ofInstances E
    Nonempty ((realPowerTwist (T.determinantNorm n) t P).Equiv
      ((realPowerTwist (T.determinantNorm n) t P).comp (entrywiseAut σ n).toMonoidHom)) ↔
      Nonempty (P.Equiv (P.comp (entrywiseAut σ n).toMonoidHom)) := by
  dsimp only
  let χ := realPowerCharacter ((LocalFieldData.ofInstances E).determinantNorm n) t
  change Nonempty ((twist χ P).Equiv ((twist χ P).comp
    (entrywiseAut σ n).toMonoidHom)) ↔ _
  rw [twist_comp, realPowerDet_comp_entrywiseAut σ t n]
  constructor
  · rintro ⟨e⟩
    have e' := twistEquiv χ⁻¹ e
    rw [twist_inv_twist, twist_inv_twist] at e'
    exact ⟨e'⟩
  · rintro ⟨e⟩
    exact ⟨twistEquiv χ e⟩

set_option maxHeartbeats 800000 in
/-- Twisting all conjugates by one real determinant power agrees with twisting
 the actual normalized induced representation. -/
def sigmaOrbitProduct_realPowerTwistEquiv (s : ℕ) (hn : 0 < n) (t : ℝ) :
    let T := LocalFieldData.ofInstances E
    (realPowerTwist (T.determinantNorm (s * n)) t (sigmaOrbitProduct σ s hn P)).Equiv
      (sigmaOrbitProduct σ s hn (realPowerTwist (T.determinantNorm n) t P)) := by
  let T := LocalFieldData.ofInstances E
  let B := BlockShape.uniform s n hn
  let ρ (i : Fin B.length) : Representation ℂ (GeneralLinear n E) W :=
    P.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom
  let ψ : Induction.SmoothCharacter ℂ Eˣ := by
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    exact ⟨realPowerCharacter T.normalizedAbsUnits t,
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits t⟩
  have ei (i : Fin B.length) :
      (twist (ψ.toMonoidHom.comp (determinant : GeneralLinear n E →* Eˣ)) (ρ i)).Equiv
        ((realPowerTwist (T.determinantNorm n) t P).comp
          (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom) := by
    unfold realPowerTwist
    rw [twist_comp, realPowerDet_comp_entrywiseAut (σ ^ (i : ℕ)) t n]
    exact Representation.Equiv.refl _
  exact (T.normalizedProductDeterminantTwistEquiv B ψ ρ).trans
    (T.normalizedProductInducedEquiv B ei)

/-- An irreducible supercuspidal can be made unitarizable by a real determinant
 power defined using the original local-field data. -/
theorem exists_unitary_realPowerTwist [CharZero E] (hn : 0 < n)
    (hP : P.IsIrreducible) (hsc : IsSupercuspidal P) :
    ∃ t : ℝ,
      let T := LocalFieldData.ofInstances E
      let Q := realPowerTwist (T.determinantNorm n) t P
      Q.IsIrreducible ∧ IsSupercuspidal Q ∧ IsUnitarizable Q := by
  let T := LocalFieldData.ofInstances E
  let := T.generalLinearTopologicalGroup n
  let p := CharZeroLocalField.residueChar E
  let : Fact p.Prime := ⟨CharZeroLocalField.residueChar_prime E⟩
  let L := CharZeroLocalField.padicField E
  let S := CharZeroLocalField.topologicalData E
  obtain ⟨t, hu⟩ := supercuspidalRealUnitarization.{v,uW} p L S n hn W P hP hsc
  let χ := realPowerCharacter (T.determinantNorm n) t
  have hχ : IsOpen (χ.ker : Set (GeneralLinear n E)) :=
    isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) t
  have hdet : (determinant : GeneralLinear n E →* Eˣ).ker ≤ χ.ker :=
    GeneralLinear.ker_determinant_le_ker_comp (realPowerCharacter T.normalizedAbsUnits t)
  exact ⟨t, (isIrreducible_twist_iff χ P).mpr hP,
    (isSupercuspidal_twist_iff χ hχ hdet P).mpr hsc, hu⟩

end Langlands.BaseChange
