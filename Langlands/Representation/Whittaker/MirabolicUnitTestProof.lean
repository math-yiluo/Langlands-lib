import Langlands.Representation.Whittaker.MirabolicUnitTestStatement
import Langlands.Representation.Twist.ContinuousCharacterProof

/-!
# Compact opposite-character mirabolic test functions: proof

A compact open ambient subgroup is chosen inside the determinant-norm-one
locus and inside a neighborhood on which the standard character is trivial.
Its mirabolic intersection is the right stabilizer, and the character values
on the corresponding `N`-cosets are extended by zero.
-/

noncomputable section

open Topology

namespace Langlands.Whittaker

universe uF uG

namespace MirabolicUnitTest

variable {G : Type uG} [Group G]

open Classical in
/-- The function equal to `θ u` at `u * k`, for `u ∈ N` and `k ∈ H`, and to zero
off `N * H`. It is representative independent when `θ` is trivial on `N ⊓ H`. -/
def cosetExtension (N H : Subgroup G) (θ : N →* ℂˣ) (g : G) : ℂ :=
  if h : ∃ u : N, (u : G)⁻¹ * g ∈ H then (θ h.choose : ℂ) else 0

variable {N H : Subgroup G} {θ : N →* ℂˣ}

/-- The prescribed value on every product `u * k`. -/
theorem cosetExtension_mul (hθ : ∀ u : N, (u : G) ∈ H → θ u = 1)
    (u : N) {k : G} (hk : k ∈ H) :
    cosetExtension N H θ (u * k) = θ u := by
  have h : ∃ v : N, (v : G)⁻¹ * (u * k) ∈ H := ⟨u, by simpa using hk⟩
  rw [cosetExtension, dite_eq_left h]
  have hv := h.choose_spec
  have hvu : ((h.choose⁻¹ * u : N) : G) ∈ H := by
    have he : ((h.choose⁻¹ * u : N) : G) = ((h.choose : G)⁻¹ * (u * k)) * k⁻¹ := by
      simp [mul_assoc]
    rw [he]
    exact H.mul_mem hv (H.inv_mem hk)
  have h1 := hθ _ hvu
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1]

/-- Outside `N * H` the extension vanishes. -/
theorem cosetExtension_eq_zero {g : G} (hg : ¬ ∃ u : N, ∃ k ∈ H, g = u * k) :
    cosetExtension N H θ g = 0 := by
  rw [cosetExtension, dite_eq_right]
  rintro ⟨u, hu⟩
  exact hg ⟨u, _, hu, by simp⟩

/-- Left `N`-covariance by `θ`, at every point of the group. -/
theorem cosetExtension_left (hθ : ∀ u : N, (u : G) ∈ H → θ u = 1)
    (u : N) (g : G) :
    cosetExtension N H θ (u * g) = θ u * cosetExtension N H θ g := by
  by_cases h : ∃ v : N, (v : G)⁻¹ * g ∈ H
  · obtain ⟨v, hv⟩ := h
    obtain ⟨k, hk, rfl⟩ : ∃ k ∈ H, g = v * k := ⟨_, hv, by simp⟩
    rw [← mul_assoc, ← Subgroup.coe_mul, cosetExtension_mul hθ _ hk,
      cosetExtension_mul hθ _ hk, map_mul, Units.val_mul]
  · have h' : ¬ ∃ v : N, (v : G)⁻¹ * (u * g) ∈ H := by
      rintro ⟨v, hv⟩
      exact h ⟨u⁻¹ * v, by simpa [mul_assoc] using hv⟩
    rw [cosetExtension, dite_eq_right h', cosetExtension, dite_eq_right h, mul_zero]

/-- Right invariance under every element of `H`. -/
theorem cosetExtension_right (hθ : ∀ u : N, (u : G) ∈ H → θ u = 1)
    (g : G) {k : G} (hk : k ∈ H) :
    cosetExtension N H θ (g * k) = cosetExtension N H θ g := by
  by_cases h : ∃ v : N, (v : G)⁻¹ * g ∈ H
  · obtain ⟨v, hv⟩ := h
    obtain ⟨k₁, hk₁, rfl⟩ : ∃ k₁ ∈ H, g = v * k₁ := ⟨_, hv, by simp⟩
    rw [mul_assoc, cosetExtension_mul hθ _ (H.mul_mem hk₁ hk),
      cosetExtension_mul hθ _ hk₁]
  · have h' : ¬ ∃ v : N, (v : G)⁻¹ * (g * k) ∈ H := by
      rintro ⟨v, hv⟩
      exact h ⟨v, by simpa [mul_assoc] using H.mul_mem hv (H.inv_mem hk)⟩
    rw [cosetExtension, dite_eq_right h', cosetExtension, dite_eq_right h]

end MirabolicUnitTest

open MirabolicUnitTest

/-- Compact opposite-character mirabolic test functions exist for every supplied
p-adic realization, every unitary additive character and every rank. -/
theorem mirabolicUnitTest {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : MirabolicUnitTestStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro ψ G P N χ
  have hker : IsOpen (χ.ker : Set N) := by
    let := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character χ
      (standardCharacterContinuous ψ n).continuous
  have hK1 : (χ.ker : Set N) ∈ 𝓝 (1 : N) := hker.mem_nhds χ.ker.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hK1
  obtain ⟨O, hO, hOK⟩ := hK1
  have hU : O ∩ ((T.determinantNorm (n + 1)).ker : Set G) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hO ((T.isOpen_ker_determinantNorm (n + 1)).mem_nhds (one_mem _))
  obtain ⟨J₀, hJc, hJU⟩ := T.generalLinearCompactOpen (n + 1) _ hU
  let P₀ : OpenSubgroup P := OpenSubgroup.comap P.subtype continuous_subtype_val J₀
  let H : Subgroup G := J₀.toSubgroup ⊓ P
  have hθ : ∀ u : N, (u : G) ∈ H → χ u = 1 := fun u hu =>
    MonoidHom.mem_ker.mp (hOK (hJU (Subgroup.mem_inf.mp hu).1).1)
  have hθ' : ∀ u : N, (u : G) ∈ H → inverseStandardCharacter ψ n u = 1 := by
    intro u hu
    change (χ u)⁻¹ = 1
    rw [hθ u hu, inv_one]
  have hH (k : P₀) : k.val.val ∈ H := Subgroup.mem_inf.mpr ⟨k.property, k.val.property⟩
  let φ : RankinSelberg.WhittakerFunctions ψ n :=
    ⟨cosetExtension N H χ, fun u g => cosetExtension_left hθ u g⟩
  let φ' : RankinSelberg.InverseWhittakerFunctions ψ n :=
    ⟨cosetExtension N H (inverseStandardCharacter ψ n),
      fun u g => cosetExtension_left hθ' u g⟩
  refine ⟨P₀, φ, φ', J₀, ?_⟩
  intro C S
  refine ⟨?_, hJc, ?_, ?_, ?_, ?_, ?_⟩
  · exact (GeneralLinear.Mirabolic.isClosed (F := F.Carrier) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hJc
  · intro k
    exact MonoidHom.mem_ker.mp (hJU k.property).2
  · intro j hj hP
    exact ⟨⟨j, hP⟩, hj, rfl⟩
  · intro u k
    exact ⟨cosetExtension_mul hθ u (hH k),
      (cosetExtension_mul hθ' u (hH k)).trans (Units.val_inv_eq_inv_val _)⟩
  · intro g hg
    have hg' : ¬ ∃ u : N, ∃ k ∈ H, g = u * k := by
      rintro ⟨u, k, hk, rfl⟩
      exact hg ⟨u, ⟨⟨k, (Subgroup.mem_inf.mp hk).2⟩, (Subgroup.mem_inf.mp hk).1⟩, rfl⟩
    exact ⟨cosetExtension_eq_zero hg', cosetExtension_eq_zero hg'⟩
  · intro g k
    exact ⟨cosetExtension_right hθ g (hH k), cosetExtension_right hθ' g (hH k)⟩

end Langlands.Whittaker
