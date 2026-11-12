import Langlands.Global.Factors.RelativeIsometryOperationStatement
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.VirtualRepresentation.Supercuspidal.Unramified
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Unramified field characters on both sides of the correspondence

For the unramified quasi-character of a p-adic field `K` with value `w` at the
chosen uniformizer, its pullback along a geometric reciprocity candidate is the
unramified Weil character with value `w` at geometric Frobenius, and twisting
by its composite with the determinant is the published unramified twist of
supercuspidal classes. Twisting a unitary supercuspidal class by `w` gives a
unitary class only when `‖w‖ = 1`.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation

universe uK uW uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartTwistBridgeFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The unramified quasi-character of `K` with value `w` at the uniformizer. -/
abbrev fieldUnramified (w : ℂˣ) : QuasiCharacter K :=
  K.canonicalTopologicalData.unramifiedCharacterContinuous w

@[simp]
theorem fieldUnramified_apply (w : ℂˣ) (a : K.Carrierˣ) :
    fieldUnramified K w a = w ^ K.canonicalTopologicalData.ord (a : K.Carrier) := rfl

/-- `‖w‖ = 1` makes the unramified field character unitary. -/
theorem norm_fieldUnramified {w : ℂˣ} (hw : ‖(w : ℂ)‖ = 1) (a : K.Carrierˣ) :
    ‖(fieldUnramified K w a : ℂ)‖ = 1 := by
  rw [fieldUnramified_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hw, one_zpow]

/-- Under a geometric candidate, the pullback of the unramified field character
with value `w` is the unramified Weil character with value `w`. -/
theorem weilCharacter_fieldUnramified {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) (w : ℂˣ) :
    LocalFactor.RankOne.weilCharacter K e (fieldUnramified K w) =
      Weil.Local.localUnramifiedCharacter K w := by
  have h := weilCharacter_eq_localUnramifiedCharacter K he
    (χ := fieldUnramified K w) (K.canonicalTopologicalData.isUnramifiedCharacter w)
  have hw : (fieldUnramified K w) K.canonicalTopologicalData.uniformizerUnit = w :=
    K.canonicalTopologicalData.unramifiedCharacter_uniformizer w
  rw [hw] at h
  ext g
  exact congrArg (fun χ : Weil.Local.localWeilGroup K →* ℂˣ => (χ g : ℂ)) h

/-- The determinant pullback of the unramified field character is the published
determinant unramified character. -/
theorem determinantQuasiCharacter_fieldUnramified (n : ℕ+) (w : ℂˣ) :
    determinantQuasiCharacter K n (fieldUnramified K w) =
      K.canonicalTopologicalData.determinantUnramifiedCharacter n w :=
  rfl

/-- The unitary Weil twist by the unramified field character with modulus-one value
`w` is the unramified twist by `w`. -/
theorem unitaryFieldCharacterTwist_fieldUnramified_val {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) {w : ℂˣ} (hw : ‖(w : ℂ)‖ = 1)
    (b : LocalWeil.UnitaryBasis.{uK, uW} K) :
    LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e (fieldUnramified K w)
        (norm_fieldUnramified K hw) (generator b) =
      generator (LocalWeil.unitaryTwistBasisEquiv K (LocalFactor.RankOne.weilCharacter K e
        (fieldUnramified K w)) (LocalWeil.norm_weilCharacter_eq_one K e _
          (norm_fieldUnramified K hw)) b) ∧
    (LocalWeil.unitaryTwistBasisEquiv K (LocalFactor.RankOne.weilCharacter K e
        (fieldUnramified K w)) (LocalWeil.norm_weilCharacter_eq_one K e _
          (norm_fieldUnramified K hw)) b).val =
      Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K w) b.val := by
  refine ⟨LocalWeil.unitaryTwistLatticeEquiv_generator K _ _ b, ?_⟩
  rw [LocalWeil.unitaryTwistBasisEquiv_val, weilCharacter_fieldUnramified K he]
  rfl

/-- The unitary supercuspidal twist by the unramified field character with
modulus-one value `w` is the unramified twist by `w`. -/
theorem unitaryCharacterTwist_fieldUnramified {w : ℂˣ} (hw : ‖(w : ℂ)‖ = 1)
    (π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K) :
    ∃ π' : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K (fieldUnramified K w)
          (norm_fieldUnramified K hw) (generator π) = generator π' ∧
        π'.val = PadicSupercuspidal.unramifiedTwistBasisEquiv K w π.val := by
  refine ⟨_, Supercuspidal.unitaryTwistLatticeEquiv_generator _ _ _ _ π, ?_⟩
  rfl

/-- A vector scaled by `c` under an operator preserving a positive definite form
forces `‖c‖ = 1`. -/
theorem norm_eq_one_of_invariantPositiveForm {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ) {g : G} {c : ℂ}
    {v : V} (hv : v ≠ 0) (h : ρ g v = c • v) : ‖c‖ = 1 := by
  let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
  let : Inner ℂ V := ⟨b.inner⟩
  have hb : b.inner v v ≠ 0 := fun h0 => hv (b.definite v h0)
  have hinvariant := b.invariant g v v
  rw [h] at hinvariant
  change inner ℂ (c • v) (c • v) = inner ℂ v v at hinvariant
  rw [InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right] at hinvariant
  have hproduct : starRingEnd ℂ c * c = 1 := by
    apply mul_right_cancel₀ hb
    simpa only [mul_assoc, one_mul] using hinvariant
  have h' := congrArg norm hproduct
  change ‖star c * c‖ = ‖(1 : ℂ)‖ at h'
  simp only [norm_mul, norm_star, norm_one] at h'
  nlinarith [norm_nonneg c]

/-- If a unitary supercuspidal class and its unramified twist by `w` are both
unitary, then `‖w‖ = 1`: the uniformizer scalar acts by a Schur scalar `c` on
the class and by `w ^ n c` on its twist, and both have modulus one. -/
theorem norm_eq_one_of_unramifiedTwist_unitary {w : ℂˣ}
    (π π' : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)
    (h : π'.val = PadicSupercuspidal.unramifiedTwistBasisEquiv K w π.val) :
    ‖(w : ℂ)‖ = 1 := by
  let T := K.canonicalTopologicalData
  rcases π with ⟨⟨n, c⟩, hπ⟩
  rcases π' with ⟨b', hπ'⟩
  simp only at h
  subst h
  obtain ⟨A, rfl⟩ := Quotient.exists_rep c
  obtain ⟨bA⟩ : Langlands.IsUnitarizable A.obj.representation := hπ
  obtain ⟨bT⟩ : Langlands.IsUnitarizable (Langlands.twist
      (T.determinantUnramifiedCharacter n w) A.obj.representation) := hπ'
  let := K.canonicalGeneralLinearTopology (n : ℕ)
  let := K.canonicalGeneralLinearTopologicalGroup (n : ℕ)
  obtain ⟨χc, ⟨-, hact⟩, -⟩ :=
    admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
  let := A.property.1
  let : Nontrivial A.obj := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GeneralLinear (n : ℕ) K.Carrier)) A.obj.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A.obj)
  let z₀ := GeneralLinear.scalarToCenter (n := (n : ℕ)) (R := K.Carrier) T.uniformizerUnit
  have h1 : A.obj.representation (z₀ : GeneralLinear n K.Carrier) v = (χc z₀ : ℂ) • v :=
    hact z₀ v
  have hn1 := norm_eq_one_of_invariantPositiveForm bA hv h1
  have h2 : Langlands.twist (T.determinantUnramifiedCharacter n w) A.obj.representation
      (z₀ : GeneralLinear n K.Carrier) v = ((w : ℂ) ^ (n : ℕ) * (χc z₀ : ℂ)) • v := by
    change ((T.determinantUnramifiedCharacter n w (GeneralLinear.scalar T.uniformizerUnit) : ℂ) •
      A.obj.representation (z₀ : GeneralLinear n K.Carrier)) v = _
    rw [LinearMap.smul_apply, h1, smul_smul,
      PadicField.TopologicalData.determinantUnramifiedCharacter_scalar,
      PadicField.TopologicalData.unramifiedCharacter_uniformizer, Units.val_pow_eq_pow_val]
  have hn2 := norm_eq_one_of_invariantPositiveForm bT hv h2
  rw [norm_mul, hn1, mul_one, norm_pow] at hn2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) n.ne_zero).mp hn2

end Langlands.Henniart.Extension
