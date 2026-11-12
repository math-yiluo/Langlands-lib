import Langlands.Correspondence.HenniartTwistIndependenceProof
import Langlands.Correspondence.HenniartNumericalStatement

/-!
# The extension of the stable images in one rank

Henniart (2000), §4.4, in a single rank `n`. Every irreducible class of the local
Weil group of dimension `n` is an unramified twist `z · b₀` of a unitary class
`b₀` factoring through a finite quotient. If every such class of dimension `n`
has a stable image, `z · b₀` is sent to the twist by `z` of the stable image of
`b₀`. Unramified-twist independence makes this independent of the decomposition.
The resulting map of rank-`n` classes is injective and commutes with unramified
twists.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartRankExtensionFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- Stable images in the rank of `b` give a stable decomposition of `b`. -/
theorem exists_stableDecomposition_of_rank {b : LocalWeil.Basis.{uK, uW} K}
    (hS : StableExistsAt.{uK, uW, uV, uE} K b.1) :
    ∃ (z : ℂˣ) (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)
      (b₀ : LocalWeil.UnitaryBasis.{uK, uW} K),
        IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀ := by
  obtain ⟨z, b₀, Q, hQ, hQf, q, hq, hb, -⟩ :=
    LocalWeil.unramifiedTwistFiniteFactoring.{uK, uW} p K b
  have hrank : b₀.val.1 = b.1 := by
    rw [← hb]
    rfl
  obtain ⟨y, hy⟩ := hS b₀ hrank ⟨Q, hQ, hQf, q, hq⟩
  obtain ⟨π₀, rfl, -⟩ := hy.exists_generator K
  exact ⟨z, π₀, b₀, hb, hy⟩

/-- Two stable decompositions of one class give the same twisted image. -/
theorem twist_eq_of_stableDecomposition
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {b : LocalWeil.Basis.{uK, uW} K} {z z' : ℂˣ} {b₀ b₀' : LocalWeil.UnitaryBasis.{uK, uW} K}
    {π₀ π₀' : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀)
    (h' : IsStableDecomposition.{uK, uW, uV, uE} K b z' b₀' π₀') :
    PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val =
      PadicSupercuspidal.unramifiedTwistBasisEquiv K z' π₀'.val := by
  have hgen := hUTI p K b z z' b₀ b₀' (generator π₀) (generator π₀')
    (IsStableDecomposition.eq_twist_inv K h) (IsStableDecomposition.eq_twist_inv K h') h.2 h'.2
  have hinc : ∀ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      PadicSupercuspidal.includeUnitary K (generator π) = generator π.val := by
    intro π
    simp [PadicSupercuspidal.includeUnitary, Supercuspidal.includeUnitary, includeSubset,
      VirtualRepresentation.map, generator]
  rw [hinc, hinc, PadicSupercuspidal.unramifiedTwistLatticeEquiv_generator,
    PadicSupercuspidal.unramifiedTwistLatticeEquiv_generator] at hgen
  exact Finsupp.single_left_injective one_ne_zero hgen

/-- Two stable decompositions with the same twisted image decompose the same class. -/
theorem eq_of_stableDecomposition (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    {b b' : LocalWeil.Basis.{uK, uW} K} {z z' : ℂˣ}
    {b₀ b₀' : LocalWeil.UnitaryBasis.{uK, uW} K}
    {π₀ π₀' : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀)
    (h' : IsStableDecomposition.{uK, uW, uV, uE} K b' z' b₀' π₀')
    (hbb' : PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val =
      PadicSupercuspidal.unramifiedTwistBasisEquiv K z' π₀'.val) : b = b' := by
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
  have hbval : Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K w) b₀.val =
      b₀'.val := by
    rw [← hb]
    exact ((unitaryFieldCharacterTwist_fieldUnramified_val K he hw b₀).2).symm
  rw [← h.1, ← h'.1, ← hbval, ← Equiv.trans_apply, Weil.twistBasisEquiv_mul,
    localUnramifiedCharacter_mul, hw_def, mul_inv_cancel_left]

/-- A stable decomposition of `b` gives one of every unramified twist of `b`. -/
theorem IsStableDecomposition.twist {b : LocalWeil.Basis.{uK, uW} K} {z : ℂˣ}
    {b₀ : LocalWeil.UnitaryBasis.{uK, uW} K} {π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableDecomposition.{uK, uW, uV, uE} K b z b₀ π₀) (w : ℂˣ) :
    IsStableDecomposition.{uK, uW, uV, uE} K
      (Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K w) b) (w * z) b₀ π₀ := by
  refine ⟨?_, h.2⟩
  rw [← h.1, ← Equiv.trans_apply, Weil.twistBasisEquiv_mul, localUnramifiedCharacter_mul]

section Rank

variable {n : ℕ+}

/-- The extension of the stable images of rank `n`, as a map to supercuspidal basis
classes: a chosen stable decomposition `σ = z · b₀` goes to `z` times the stable
image of `b₀`. -/
def rankExtensionBasis (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (σ : IrreducibleWeilClass.{uK, uW} K n) : PadicSupercuspidal.Basis.{uK, uV} K :=
  PadicSupercuspidal.unramifiedTwistBasisEquiv K
    (exists_stableDecomposition_of_rank K (b := ⟨n, σ⟩) hS).choose
    (exists_stableDecomposition_of_rank K (b := ⟨n, σ⟩) hS).choose_spec.choose.val

theorem rankExtensionBasis_spec (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (σ : IrreducibleWeilClass.{uK, uW} K n) :
    ∃ (z : ℂˣ) (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K)
      (b₀ : LocalWeil.UnitaryBasis.{uK, uW} K),
      IsStableDecomposition.{uK, uW, uV, uE} K ⟨n, σ⟩ z b₀ π₀ ∧
        rankExtensionBasis K hS σ = PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val :=
  ⟨_, _, _, (exists_stableDecomposition_of_rank K (b := ⟨n, σ⟩) hS).choose_spec.choose_spec.choose_spec,
    rfl⟩

/-- The extension does not depend on the stable decomposition. -/
theorem rankExtensionBasis_eq (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {σ : IrreducibleWeilClass.{uK, uW} K n} {z : ℂˣ} {b₀ : LocalWeil.UnitaryBasis.{uK, uW} K}
    {π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableDecomposition.{uK, uW, uV, uE} K ⟨n, σ⟩ z b₀ π₀) :
    rankExtensionBasis K hS σ = PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val := by
  obtain ⟨z₁, π₁, b₁, h₁, he⟩ := rankExtensionBasis_spec K hS σ
  rw [he]
  exact twist_eq_of_stableDecomposition K hUTI h₁ h

/-- The extension preserves rank. -/
theorem rankExtensionBasis_rank (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (σ : IrreducibleWeilClass.{uK, uW} K n) : (rankExtensionBasis K hS σ).1 = n := by
  obtain ⟨z, π₀, b₀, h, he⟩ := rankExtensionBasis_spec K hS σ
  rw [he, PadicSupercuspidal.unramifiedTwistBasisEquiv_rank]
  obtain ⟨π, hπ, hrank⟩ := h.2.exists_generator K
  have : π = π₀ := (Finsupp.single_left_injective (one_ne_zero (α := ℤ)) hπ).symm
  subst this
  rw [hrank]
  exact congrArg Sigma.fst h.1

/-- Henniart's extension of the stable images in rank `n`, as a map of rank-`n`
classes. -/
def rankExtension (hS : StableExistsAt.{uK, uW, uV, uE} K n) :
    IrreducibleWeilClass.{uK, uW} K n → SupercuspidalAutomorphicClass.{uK, uV} K n :=
  fun σ => rankCast K (rankExtensionBasis K hS σ) (rankExtensionBasis_rank K hS σ)

theorem sigma_rankExtension (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (σ : IrreducibleWeilClass.{uK, uW} K n) :
    (⟨n, rankExtension K hS σ⟩ : PadicSupercuspidal.Basis.{uK, uV} K) =
      rankExtensionBasis K hS σ :=
  sigma_rankCast K _ _

/-- The extension in rank `n` is injective. -/
theorem rankExtension_injective (hS : StableExistsAt.{uK, uW, uV, uE} K n)
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    Function.Injective (rankExtension K hS) := by
  intro σ σ' hσσ'
  have hbasis : rankExtensionBasis K hS σ = rankExtensionBasis K hS σ' := by
    rw [← sigma_rankExtension K hS σ, ← sigma_rankExtension K hS σ', hσσ']
  obtain ⟨z, π₀, b₀, h, he₁⟩ := rankExtensionBasis_spec K hS σ
  obtain ⟨z', π₀', b₀', h', he₂⟩ := rankExtensionBasis_spec K hS σ'
  rw [he₁, he₂] at hbasis
  have hb := eq_of_stableDecomposition K hCE he h h' hbasis
  exact eq_of_heq (Sigma.mk.inj_iff.mp hb).2

end Rank

/-- The extension in rank `k + 1` commutes with the unramified twists of the
numerical theorem. -/
theorem rankExtension_twist {k : ℕ} (hS : StableExistsAt.{uK, uW, uV, uE} K k.succPNat)
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE}) (z : ℂˣ)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) :
    rankExtension K hS (Numerical.weilUnramifiedTwist K k z σ) =
      Numerical.supercuspidalUnramifiedTwist K k z (rankExtension K hS σ) := by
  obtain ⟨z₀, π₀, b₀, h, he⟩ := rankExtensionBasis_spec K hS σ
  have htw : IsStableDecomposition.{uK, uW, uV, uE} K
      ⟨k.succPNat, Numerical.weilUnramifiedTwist K k z σ⟩ (z * z₀) b₀ π₀ :=
    IsStableDecomposition.twist K h z
  have hb := rankExtensionBasis_eq K hS hUTI htw
  have key : (⟨k.succPNat, rankExtension K hS (Numerical.weilUnramifiedTwist K k z σ)⟩ :
      PadicSupercuspidal.Basis.{uK, uV} K) =
      ⟨k.succPNat, Numerical.supercuspidalUnramifiedTwist K k z (rankExtension K hS σ)⟩ := by
    rw [sigma_rankExtension, hb]
    change _ = PadicSupercuspidal.unramifiedTwistBasisEquiv K z
      ⟨k.succPNat, rankExtension K hS σ⟩
    rw [sigma_rankExtension, he, ← Equiv.trans_apply,
      PadicSupercuspidal.unramifiedTwistBasisEquiv_mul]
  exact eq_of_heq (Sigma.mk.inj_iff.mp key).2

end Langlands.Henniart.Extension
