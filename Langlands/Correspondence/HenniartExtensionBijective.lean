import Langlands.Correspondence.HenniartExtension
import Langlands.Correspondence.HenniartTwistBridge
import Langlands.Correspondence.HenniartExtensionInputs

/-!
# Bijectivity of the extended stable map

Henniart (2000), §4.4, with Henniart (1993), §4.3. Candidates send the twist
of a class by a modulus-one character to the twist of its image. Two stable
decompositions with the same image therefore differ by a modulus-one
unramified twist, and the extended map is injective. Surjectivity onto a class
of rank `n` follows from surjectivity of the stable images onto unitary classes
with finite-order central character, once every supercuspidal class is an
unramified twist of such a class.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartExtensionBijectiveFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- Twist of unitary Weil classes by the pullback of a modulus-one field character. -/
abbrev weilUnitaryTwist (e : ReciprocityCandidate K) (χ : QuasiCharacter K)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    LocalWeil.UnitaryBasis.{uK, uW} K ≃ LocalWeil.UnitaryBasis.{uK, uW} K :=
  LocalWeil.unitaryTwistBasisEquiv K (LocalFactor.RankOne.weilCharacter K e χ)
    (LocalWeil.norm_weilCharacter_eq_one K e χ hχ)

/-- Twist of unitary supercuspidal classes by a modulus-one field character
composed with the determinant. -/
abbrev supercuspidalUnitaryTwist (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    PadicSupercuspidal.UnitaryBasis.{uK, uV} K ≃ PadicSupercuspidal.UnitaryBasis.{uK, uV} K :=
  Supercuspidal.unitaryTwistBasisEquiv
    (fun n => determinantQuasiCharacter K n χ)
    (fun n => isOpen_ker_determinantQuasiCharacter K n χ)
    (fun _ => GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom)
    (fun _ _ => hχ _)

/-- A candidate sends the twist of a generator by a modulus-one character to the
twist of its image. -/
theorem candidate_twist_generator {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} {Φ : W ≃ₗ[ℤ] A}
    (hΦ : LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ) {e : ReciprocityCandidate K}
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    {b : LocalWeil.UnitaryBasis.{uK, uW} K} {π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (x : W) (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator b)
    (hΦx : (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = generator π) :
    ∃ x' : W, (x' : LocalWeil.UnitaryLattice.{uK, uW} K) =
        generator (weilUnitaryTwist K e χ hχ b) ∧
      (Φ x' : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) =
        generator (supercuspidalUnitaryTwist K χ hχ π) := by
  obtain ⟨hmem, hΦtw⟩ := (hΦ.1.2.2.2 e he χ hχ).1 x
  refine ⟨_, ?_, hΦtw.trans ?_⟩
  · change LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e χ hχ
      (x : LocalWeil.UnitaryLattice.{uK, uW} K) = _
    rw [hx]
    exact LocalWeil.unitaryTwistLatticeEquiv_generator K _ _ b
  · rw [hΦx]
    exact Supercuspidal.unitaryTwistLatticeEquiv_generator _ _ _ _ π

/-- Two classes with stable images have a common candidate realizing both. -/
theorem exists_common_candidate₂
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {σ₁ σ₂ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {y₁ y₂ : PadicSupercuspidal.UnitaryLattice.{uK, uV} K}
    (h₁ : IsStableImage.{uK, uW, uV, uE} K σ₁ y₁) (h₂ : IsStableImage.{uK, uW, uV, uE} K σ₂ y₂) :
    ∃ (W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K))
      (A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)) (Φ : W ≃ₗ[ℤ] A),
      LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ ∧
      (∃ x : W, (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ₁ ∧
        (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = y₁) ∧
      (∃ x : W, (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ₂ ∧
        (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = y₂) := by
  obtain ⟨W, A, Φ, hΦ, hx⟩ := exists_common_candidate K hCE
    (fun b : Bool => if b then σ₁ else σ₂) (fun b => if b then y₁ else y₂)
    (fun b => by cases b <;> simpa)
  exact ⟨W, A, Φ, hΦ, by simpa using hx true, by simpa using hx false⟩

/-- Equal images under a candidate of two generators in its domain give equal
classes. -/
theorem eq_of_candidate {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)} (Φ : W ≃ₗ[ℤ] A)
    {b b' : LocalWeil.UnitaryBasis.{uK, uW} K} {x x' : W}
    (hx : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator b)
    (hx' : (x' : LocalWeil.UnitaryLattice.{uK, uW} K) = generator b')
    (h : (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = Φ x') : b = b' := by
  have hxx : x = x' := Φ.injective (Subtype.ext h)
  subst hxx
  exact Finsupp.single_left_injective one_ne_zero (hx.symm.trans hx')

theorem localUnramifiedCharacter_mul (z w : ℂˣ) :
    Weil.Local.localUnramifiedCharacter K z * Weil.Local.localUnramifiedCharacter K w =
      Weil.Local.localUnramifiedCharacter K (z * w) := by
  ext g
  simp [Weil.Local.localUnramifiedCharacter, mul_zpow]

/-- The extended stable map is injective. -/
theorem extensionBasis_injective (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    Function.Injective (extensionBasis K hSC) := by
  intro b b' hbb'
  obtain ⟨z, π₀, b₀, h, he₁⟩ := extensionBasis_spec K hSC b
  obtain ⟨z', π₀', b₀', h', he₂⟩ := extensionBasis_spec K hSC b'
  rw [he₁, he₂] at hbb'
  set w := z'⁻¹ * z with hw_def
  have hπ' : π₀'.val = PadicSupercuspidal.unramifiedTwistBasisEquiv K w π₀.val := by
    have := congrArg (PadicSupercuspidal.unramifiedTwistBasisEquiv K z'⁻¹) hbb'
    rw [← Equiv.trans_apply, ← Equiv.trans_apply,
      PadicSupercuspidal.unramifiedTwistBasisEquiv_mul,
      PadicSupercuspidal.unramifiedTwistBasisEquiv_mul, inv_mul_cancel,
      PadicSupercuspidal.unramifiedTwistBasisEquiv_one] at this
    exact this.symm
  have hw : ‖(w : ℂ)‖ = 1 := norm_eq_one_of_unramifiedTwist_unitary K π₀ π₀' hπ'
  obtain ⟨W, A, Φ, hΦ, ⟨x, hx, hΦx⟩, ⟨x', hx', hΦx'⟩⟩ := exists_common_candidate₂ K hCE h.2 h'.2
  obtain ⟨x'', hx'', hΦx''⟩ := candidate_twist_generator K hΦ he (fieldUnramified K w)
    (norm_fieldUnramified K hw) x hx hΦx
  have hsc : supercuspidalUnitaryTwist K (fieldUnramified K w) (norm_fieldUnramified K hw) π₀ =
      π₀' := Subtype.ext hπ'.symm
  rw [hsc, ← hΦx'] at hΦx''
  have hb : weilUnitaryTwist K e (fieldUnramified K w) (norm_fieldUnramified K hw) b₀ = b₀' :=
    eq_of_candidate K Φ hx'' hx' hΦx''
  have hbval : Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K w) b₀.val = b₀'.val := by
    rw [← hb]
    exact ((unitaryFieldCharacterTwist_fieldUnramified_val K he hw b₀).2).symm
  rw [← h.1, ← h'.1, ← hbval, ← Equiv.trans_apply, Weil.twistBasisEquiv_mul,
    localUnramifiedCharacter_mul, hw_def, mul_inv_cancel_left]

/-- Every supercuspidal class is in the image of the extended stable map. -/
theorem extensionBasis_surjective (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    (hunit : SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV}) :
    Function.Surjective (extensionBasis K hSC) := by
  intro π
  obtain ⟨z, π₀, hω, rfl⟩ := hunit p K π
  obtain ⟨b₀, hrank, hb₀⟩ := (hSC p K π₀.val.1).2 π₀ rfl hω
  refine ⟨Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z) b₀.val, ?_⟩
  exact extensionBasis_eq K hSC hUTI ⟨rfl, hb₀⟩

/-- The extended stable map is bijective in every rank. -/
theorem extensionMap_rankwiseBijective (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    (hunit : SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    SupercuspidalRankwiseBijective K (extensionMap K hSC) := by
  intro n
  constructor
  · intro σ σ' h
    have h' : extensionBasis K hSC ⟨n, σ⟩ = extensionBasis K hSC ⟨n, σ'⟩ := by
      rw [← sigma_extensionMap, ← sigma_extensionMap, h]
    exact eq_of_heq (Sigma.mk.inj (extensionBasis_injective K hCE hSC he h')).2
  · intro π
    obtain ⟨⟨m, σ⟩, hb⟩ := extensionBasis_surjective K hSC hUTI hunit ⟨n, π⟩
    have hm : m = n := by
      have := extensionBasis_rank K hSC ⟨m, σ⟩
      rw [hb] at this
      exact this.symm
    subst hm
    refine ⟨σ, ?_⟩
    have h' := (sigma_extensionMap K hSC m σ).trans hb
    exact eq_of_heq (Sigma.mk.inj h').2

end Langlands.Henniart.Extension
