import Langlands.BaseChange.TwistedVanDijk.Operator
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Existence of levels

Every test function on `GL_n(E)` has a level: a compact open subgroup of `GL_n(𝒪_E)`, stable
under `σ` and `σ⁻¹`, under which it is invariant on both sides. For `n ≥ 1` a principal
congruence subgroup works; for `n = 0` the group is trivial. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory GeneralLinear HarmonicAnalysis

universe u v

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

/-- `σ` restricted to the valuation ring of `E`. -/
def integerRingEquiv (σ : E ≃ₐ[F] E) :
    (ValuativeRel.valuation E).integer ≃+* (ValuativeRel.valuation E).integer where
  toFun x := ⟨σ x, (algEquiv_mem_integer_iff σ x).mpr x.property⟩
  invFun x := ⟨σ.symm x, (algEquiv_mem_integer_iff σ.symm x).mpr x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : E) y)
  map_add' x y := Subtype.ext (map_add σ (x : E) y)

theorem integerRingEquiv_mem_maximalIdeal_pow (σ : E ≃ₐ[F] E) (a : ℕ)
    {x : (ValuativeRel.valuation E).integer}
    (hx : x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation E).integer ^ a) :
    integerRingEquiv σ x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation E).integer ^ a := by
  have h1 : (IsLocalRing.maximalIdeal (ValuativeRel.valuation E).integer ^ a).map
      (integerRingEquiv σ : (ValuativeRel.valuation E).integer →+*
        (ValuativeRel.valuation E).integer) ≤
      IsLocalRing.maximalIdeal (ValuativeRel.valuation E).integer ^ a := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) a
  exact h1 (Ideal.mem_map_of_mem _ hx)

/-- Principal congruence subgroups are stable under the entrywise action of `σ`. -/
theorem entrywiseAut_mem_principalLevelSubgroup (σ : E ≃ₐ[F] E) (n a : ℕ)
    {g : GeneralLinear (n + 1) E} (hg : g ∈ Conductor.principalLevelSubgroup E n a) :
    entrywiseAut σ (n + 1) g ∈ Conductor.principalLevelSubgroup E n a := by
  rw [Conductor.principalLevelSubgroup, Conductor.mem_principalCongruenceSubgroup_iff] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  have hone : ∀ i j : Fin (n + 1),
      σ ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) i j) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) i j := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨x, hx, hxe⟩ := h1 i j
    refine ⟨integerRingEquiv σ x, integerRingEquiv_mem_maximalIdeal_pow σ a hx, ?_⟩
    change σ x = _
    rw [hxe, map_sub, hone, entrywiseAut_apply_apply]
  · obtain ⟨x, hx, hxe⟩ := h2 i j
    refine ⟨integerRingEquiv σ x, integerRingEquiv_mem_maximalIdeal_pow σ a hx, ?_⟩
    change σ x = _
    rw [hxe, map_sub, hone, ← map_inv, entrywiseAut_apply_apply]

/-- Every test function on `GL_n(E)` has a level. -/
theorem exists_level (σ : E ≃ₐ[F] E) {n : ℕ} (φ : SchwartzBruhat (GeneralLinear n E)) :
    Nonempty (Level σ ⇑φ) := by
  cases n with
  | zero =>
    have hsub : Subsingleton (GeneralLinear 0 E) := by
      constructor
      intro a b
      apply Units.ext
      ext i
      exact i.elim0
    refine ⟨⟨⊤, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro g _
      rw [GeneralLinearGroup.mem_integralSubgroup]
      exact ⟨fun i => i.elim0, fun i => i.elim0⟩
    · intro k _
      trivial
    · intro k _
      trivial
    · intro k _ x
      rw [Subsingleton.elim (k * x) x]
    · intro x k _
      rw [Subsingleton.elim (x * k) x]
  | succ n =>
    have := LocalFieldTopology.generalLinear_t2Space E (n + 1)
    have := LocalFieldTopology.generalLinear_locallyCompactSpace E (n + 1)
    have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (n + 1)
    obtain ⟨K'', -, -, hK''⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance
      (GeneralLinear (n + 1) E) {φ} ⊤
    have hφ := hK'' φ (Finset.mem_singleton_self φ)
    obtain ⟨a, -, ha⟩ := Conductor.principalLevelCofinal E n (K'' : Set (GeneralLinear (n + 1) E))
      (K''.isOpen.mem_nhds K''.one_mem)
    refine ⟨⟨Conductor.principalLevelOpenSubgroup E n a, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro g hg
      have h0 := Conductor.principalLevelSubgroup_antitone E n (Nat.zero_le a) hg
      rw [Conductor.principalLevelSubgroup_zero, Conductor.mem_integralSubgroup] at h0
      exact (GeneralLinearGroup.mem_integralSubgroup _ _ _).mpr h0
    · intro k hk
      exact entrywiseAut_mem_principalLevelSubgroup σ n a hk
    · intro k hk
      exact entrywiseAut_mem_principalLevelSubgroup σ.symm n a hk
    · intro k hk x
      exact hφ.1 ⟨k, ha hk⟩ x
    · intro x k hk
      exact hφ.2 ⟨k, ha hk⟩ x

end Langlands.BaseChange.TwistedVanDijk
