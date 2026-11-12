import Langlands.Correspondence.HenniartExtensionBijective

/-!
# Character twists and the extended stable map

Henniart (1993), §4.3–4.4. For a quasi-character `χ` of `K^×` and a stable
decomposition `b = z · b₀`, decompose the twist of `b₀` by `χ ∘ rec` as `w · u₁`
with `u₁` unitary of finite image. Then `χ₁ = χ · |unramified w|⁻¹` takes values of
modulus one, because `b₀` and its `χ₁`-twist `u₁` are both unitary. A common
candidate for `b₀` and `u₁` identifies the stable image of `u₁` with the
`χ₁`-twist of the stable image of `b₀`. Collecting the unramified parameters
gives twist compatibility for every quasi-character.
-/

noncomputable section

namespace Langlands.VirtualRepresentation.Supercuspidal

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- Rank-wise twists by equal characters agree. -/
theorem twistBasisEquiv_congr {χ χ' : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ} (h : χ = χ')
    (hχ : ∀ n : ℕ+, IsOpen ((χ n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdet : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (χ n).ker)
    (hχ' : ∀ n : ℕ+, IsOpen ((χ' n).ker : Set (GeneralLinear (n : ℕ) F)))
    (hdet' : ∀ n : ℕ+, (GeneralLinear.determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤
      (χ' n).ker) :
    twistBasisEquiv.{uF, uV} χ hχ hdet = twistBasisEquiv χ' hχ' hdet' := by
  subst h
  rfl

end Langlands.VirtualRepresentation.Supercuspidal

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartExtensionTwistFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The rank-wise twist of supercuspidal classes by `χ ∘ det`. -/
abbrev supercuspidalTwistBasis (χ : QuasiCharacter K) :
    PadicSupercuspidal.Basis.{uK, uV} K ≃ PadicSupercuspidal.Basis.{uK, uV} K :=
  Supercuspidal.twistBasisEquiv (fun n => determinantQuasiCharacter K n χ)
    (fun n => isOpen_ker_determinantQuasiCharacter K n χ)
    (fun _ => GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom)

/-- The reciprocity homomorphism is surjective. -/
theorem reciprocityHom_surjective' (e : ReciprocityCandidate K) :
    Function.Surjective (reciprocityHom K e) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm a)
  refine ⟨x, ?_⟩
  change e (QuotientGroup.mk x) = a
  rw [hx]
  exact e.apply_symm_apply a

theorem weilCharacter_mul (e : ReciprocityCandidate K) (χ η : QuasiCharacter K) :
    LocalFactor.RankOne.weilCharacter K e (χ * η) =
      LocalFactor.RankOne.weilCharacter K e χ * LocalFactor.RankOne.weilCharacter K e η :=
  rfl

/-- Rank-wise twists by `χ ∘ det` and `η ∘ det` compose to the twist by
`(χ * η) ∘ det`. -/
theorem supercuspidalTwistBasis_mk (χ : QuasiCharacter K) (n : ℕ+)
    (c : SupercuspidalAutomorphicClass.{uK, uV} K n) :
    supercuspidalTwistBasis K χ ⟨n, c⟩ = ⟨n, supercuspidalTwist K χ c⟩ :=
  rfl

theorem supercuspidalTwistBasis_comp (χ η : QuasiCharacter K)
    (π : PadicSupercuspidal.Basis.{uK, uV} K) :
    supercuspidalTwistBasis K χ (supercuspidalTwistBasis K η π) =
      supercuspidalTwistBasis K (χ * η) π := by
  obtain ⟨n, c⟩ := π
  rw [supercuspidalTwistBasis_mk, supercuspidalTwistBasis_mk, supercuspidalTwistBasis_mk,
    supercuspidalTwist_twist]

/-- Characters of the local Weil group commute. -/
theorem weilCharacter_mul_comm (χ η : Weil.Local.localWeilGroup K →ₜ* ℂˣ) :
    χ * η = η * χ := by
  ext g
  change ((χ g * η g : ℂˣ) : ℂ) = ((η g * χ g : ℂˣ) : ℂ)
  rw [mul_comm]

/-- The unramified twist is the twist by the unramified field character. -/
theorem unramifiedTwistBasisEquiv_eq (z : ℂˣ) :
    PadicSupercuspidal.unramifiedTwistBasisEquiv.{uK, uV} K z =
      supercuspidalTwistBasis K (fieldUnramified K z) :=
  rfl

/-- The extended stable map commutes with twists by every quasi-character on bases. -/
theorem extensionBasis_twist (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    (χ : QuasiCharacter K) (b : LocalWeil.Basis.{uK, uW} K) :
    extensionBasis K hSC (Weil.twistBasisEquiv (LocalFactor.RankOne.weilCharacter K e χ) b) =
      supercuspidalTwistBasis K χ (extensionBasis K hSC b) := by
  obtain ⟨z, π₀, b₀, h, he₁⟩ := extensionBasis_spec K hSC b
  -- decompose the twist of `b₀`
  obtain ⟨w, u₁, Q, hQ, hQf, q, hq, hu₁, -⟩ := LocalWeil.unramifiedTwistFiniteFactoring.{uK, uW} p K
    (Weil.twistBasisEquiv (LocalFactor.RankOne.weilCharacter K e χ) b₀.val)
  obtain ⟨y₁, hy₁⟩ := (hSC p K u₁.val.1).1 u₁ rfl ⟨Q, hQ, hQf, q, hq⟩
  obtain ⟨π₁, rfl, -⟩ := hy₁.exists_generator K
  -- the modulus-one character `χ₁`
  set χ₁ := χ * fieldUnramified K w⁻¹ with hχ₁
  have hone : Weil.Local.localUnramifiedCharacter K 1 = 1 := by
    ext g
    simp [Weil.Local.localUnramifiedCharacter]
  have htw : Weil.twistBasisEquiv (LocalFactor.RankOne.weilCharacter K e χ₁) b₀.val = u₁.val := by
    have hmul : LocalFactor.RankOne.weilCharacter K e χ₁ =
        Weil.Local.localUnramifiedCharacter K w⁻¹ * LocalFactor.RankOne.weilCharacter K e χ := by
      rw [hχ₁, weilCharacter_mul, weilCharacter_fieldUnramified K he, weilCharacter_mul_comm]
    rw [hmul, ← Weil.twistBasisEquiv_mul, Equiv.trans_apply, ← hu₁, ← Equiv.trans_apply,
      Weil.twistBasisEquiv_mul, localUnramifiedCharacter_mul, inv_mul_cancel, hone,
      Weil.twistBasisEquiv_one]
    rfl
  have hχ₁norm : ∀ a, ‖(χ₁ a : ℂ)‖ = 1 := by
    intro a
    obtain ⟨g, rfl⟩ := reciprocityHom_surjective' K e a
    have := Weil.norm_eq_one_of_isUnitaryClass_twist (LocalFactor.RankOne.weilCharacter K e χ₁)
      b₀.property (htw ▸ u₁.property) g
    exact this
  -- a common candidate identifies the stable image of `u₁`
  obtain ⟨W, A, Φ, hΦ, ⟨x, hx, hΦx⟩, ⟨x₁, hx₁, hΦx₁⟩⟩ := exists_common_candidate₂ K hCE h.2 hy₁
  obtain ⟨x', hx', hΦx'⟩ := candidate_twist_generator K hΦ he χ₁ hχ₁norm x hx hΦx
  have hu₁eq : weilUnitaryTwist K e χ₁ hχ₁norm b₀ = u₁ := Subtype.ext htw
  rw [hu₁eq] at hx'
  have hxx : x' = x₁ := Subtype.ext (hx'.trans hx₁.symm)
  rw [hxx, hΦx₁] at hΦx'
  have hπ₁ : π₁ = supercuspidalUnitaryTwist K χ₁ hχ₁norm π₀ :=
    Finsupp.single_left_injective one_ne_zero hΦx'
  -- the stable decomposition of the twist of `b`
  have hdec : IsStableDecomposition.{uK, uW, uV, uE} K
      (Weil.twistBasisEquiv (LocalFactor.RankOne.weilCharacter K e χ) b) (z * w) u₁ π₁ := by
    refine ⟨?_, hy₁⟩
    rw [← localUnramifiedCharacter_mul, ← Weil.twistBasisEquiv_mul, Equiv.trans_apply, hu₁,
      ← h.1, ← Equiv.trans_apply, ← Equiv.trans_apply, Weil.twistBasisEquiv_mul,
      Weil.twistBasisEquiv_mul, weilCharacter_mul_comm]
  rw [extensionBasis_eq K hSC hUTI hdec, he₁, hπ₁]
  change supercuspidalTwistBasis K (fieldUnramified K (z * w))
      (supercuspidalTwistBasis K χ₁ π₀.val) =
    supercuspidalTwistBasis K χ (supercuspidalTwistBasis K (fieldUnramified K z) π₀.val)
  rw [supercuspidalTwistBasis_comp, supercuspidalTwistBasis_comp]
  have hχeq : fieldUnramified K (z * w) * χ₁ = χ * fieldUnramified K z := by
    ext a
    change ((fieldUnramified K (z * w) a * (χ a * fieldUnramified K w⁻¹ a) : ℂˣ) : ℂ) =
      ((χ a * fieldUnramified K z a : ℂˣ) : ℂ)
    rw [fieldUnramified_apply, fieldUnramified_apply, fieldUnramified_apply, inv_zpow, mul_zpow]
    push_cast
    have hw0 : ((w : ℂ) ^ K.canonicalTopologicalData.ord (a : K.Carrier)) ≠ 0 :=
      zpow_ne_zero _ w.ne_zero
    field_simp
  rw [hχeq]

/-- Twist compatibility of the extended stable map for every quasi-character. -/
theorem extensionMap_twist (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    SupercuspidalTwistCompatibility K e (extensionMap K hSC) := by
  rw [supercuspidalTwistCompatibility_iff]
  intro n σ χ
  have h := extensionBasis_twist K hCE hSC hUTI he χ ⟨n, σ⟩
  have h1 := sigma_extensionMap K hSC n (FiniteRepresentation.continuousIrreducibleTwistEquiv
    (LocalFactor.RankOne.weilCharacter K e χ) n σ)
  have h2 : supercuspidalTwistBasis K χ (extensionBasis K hSC ⟨n, σ⟩) =
      ⟨n, supercuspidalTwist K χ (extensionMap K hSC n σ)⟩ := by
    rw [← sigma_extensionMap]
    rfl
  exact eq_of_heq (Sigma.mk.inj (h1.trans (h.trans h2))).2

end Langlands.Henniart.Extension
