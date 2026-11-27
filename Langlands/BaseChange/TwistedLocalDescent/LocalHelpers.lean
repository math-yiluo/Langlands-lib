import Langlands.BaseChange.TwistedLocalDescent.ModularCharacter
import Langlands.BaseChange.TwistedVanDijk.Measures
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-! # Group-theoretic inputs for the local mass identity over a local field

A continuous homomorphism to `ℝ≥0` is trivial on compact subgroups. Over a nonarchimedean local
field `E`: Haar measure on `GL_n(E)` is right invariant; `p ↦ δ_P(p)^{1/2}` is a continuous
homomorphism on the standard parabolic; and, for an `F`-algebra automorphism `σ` of `E` with `E`
carrying the `F`-module topology, `δ_P^{1/2}` is invariant under `σ` and the entrywise action of
`σ` is a topological automorphism of the parabolic preserving its Haar measures. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set
open scoped _root_.Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe u v

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous homomorphism to `ℝ≥0` is trivial on a compact subgroup. -/
theorem eq_one_of_mem_compact (f : G →* ℝ≥0) (hf : Continuous f) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : f k = 1 := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
  have hbound : ∀ y ∈ K, f y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  have key : ∀ y ∈ K, ¬ 1 < f y := by
    intro y hy h1
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt M h1
    have := hbound (y ^ m) (K.pow_mem hy m)
    rw [map_pow] at this
    exact absurd this (not_le.mpr hm)
  have hne : f k ≠ 0 := ((Group.isUnit k).map f).ne_zero
  rcases lt_trichotomy (f k) 1 with h | h | h
  · exfalso
    apply key k⁻¹ (K.inv_mem hk)
    rw [map_inv]
    exact one_lt_inv₀ (pos_iff_ne_zero.mpr hne) |>.mpr h
  · exact h
  · exact absurd h (key k hk)

end Compact

section LocalField

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  TwistedVanDijk.parabolic_secondCountable TwistedVanDijk.parabolic_locallyCompact

/-- Haar measure on `GL_n(E)` is right invariant. -/
theorem isMulRightInvariant_generalLinear [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure] :
    μG.IsMulRightInvariant := by
  have hKo := TwistedVanDijk.isOpen_integralGL (E := E) n
  have hKc := TwistedVanDijk.isCompact_integralGL (E := E) n
  have hscalar : ∀ a : Eˣ, modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin n) a) = 1 := by
    intro a
    have h1 := map_mul_right_eq_modularCharacter_smul μG (Matrix.GeneralLinearGroup.scalar (Fin n) a)
    have he : (fun x : GeneralLinear n E => x * Matrix.GeneralLinearGroup.scalar (Fin n) a) =
        (fun x : GeneralLinear n E => Matrix.GeneralLinearGroup.scalar (Fin n) a * x) := by
      funext x
      exact (Matrix.GeneralLinearGroup.scalar_commute a x).symm
    rw [he, map_mul_left_eq_self] at h1
    have h2 := congrArg (fun ν : Measure (GeneralLinear n E) =>
      ν (TwistedVanDijk.integralGL E n : Set (GeneralLinear n E))) h1
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    have hpos := (hKo.measure_pos μG ⟨1, (TwistedVanDijk.integralGL E n).one_mem⟩).ne'
    have hfin := hKc.measure_lt_top (μ := μG) |>.ne
    have : (1 : ℝ≥0∞) * μG (TwistedVanDijk.integralGL E n) =
        (modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin n) a) : ℝ≥0∞) *
          μG (TwistedVanDijk.integralGL E n) := by rw [one_mul]; exact h2
    exact_mod_cast ((ENNReal.mul_left_inj hpos hfin).mp this).symm
  refine ⟨fun g => ?_⟩
  rw [map_mul_right_eq_modularCharacter_smul μG g,
    RankinSelberg.GeneralLinearUnimodularity.character_eq_one modularCharacter hscalar g,
    ENNReal.coe_one, one_smul]

/-- The half modulus `p ↦ δ_P(p)^{1/2}` on the standard parabolic. -/
def parabolicHalfModulusNNReal : B.parabolic E →* ℝ≥0 where
  toFun p := NNReal.sqrt ((LocalFieldData.ofInstances E).leviModulus B (B.leviProjection E p) : ℝ≥0)
  map_one' := by simp
  map_mul' p q := by simp [NNReal.sqrt_mul]

theorem continuous_parabolicHalfModulusNNReal :
    Continuous (parabolicHalfModulusNNReal (E := E) B) := by
  set f := parabolicHalfModulusNNReal (E := E) B
  have hker : IsOpen (((LocalFieldData.ofInstances E).leviModulus B).ker.comap
      (B.leviProjection E) : Set (B.parabolic E)) :=
    ((LocalFieldData.ofInstances E).isOpen_ker_leviModulus B).preimage
      (B.leviProjectionContinuous E).continuous
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hnhds : (fun x => g * x) '' (((LocalFieldData.ofInstances E).leviModulus B).ker.comap
      (B.leviProjection E) : Set (B.parabolic E)) ∈ 𝓝 g :=
    ((isOpenMap_mul_left g) _ hker).mem_nhds ⟨1, one_mem _, mul_one g⟩
  refine (continuousAt_const (y := f g)).congr ?_
  filter_upwards [hnhds] with x hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hk1 : (LocalFieldData.ofInstances E).leviModulus B (B.leviProjection E k) = 1 := hk
  change f g = f (g * k)
  simp only [f, parabolicHalfModulusNNReal, MonoidHom.coe_mk, OneHom.coe_mk, map_mul,
    hk1, Units.val_one, mul_one, NNReal.sqrt_one]

variable (σ : E ≃ₐ[F] E)

/-- The entrywise action of `σ` on the standard parabolic. -/
def parabolicContinuousAut : B.parabolic E ≃ₜ* B.parabolic E where
  toFun p := ⟨entrywiseAut σ n p, (entrywiseAut_mem_parabolic_iff σ B p).2 p.2⟩
  invFun p := ⟨entrywiseAut σ.symm n p, (entrywiseAut_mem_parabolic_iff σ.symm B p).2 p.2⟩
  left_inv p := Subtype.ext ((TwistedVanDijk.entrywiseContinuousAut σ n).symm_apply_apply p)
  right_inv p := Subtype.ext ((TwistedVanDijk.entrywiseContinuousAut σ n).apply_symm_apply p)
  map_mul' p q := Subtype.ext (map_mul (entrywiseAut σ n) (p : GeneralLinear n E) q)
  continuous_toFun :=
    ((TwistedVanDijk.entrywiseContinuousAut σ n).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((TwistedVanDijk.entrywiseContinuousAut σ n).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_parabolicContinuousAut (p : B.parabolic E) :
    ((parabolicContinuousAut B σ p : B.parabolic E) : GeneralLinear n E) = entrywiseAut σ n p :=
  rfl

theorem parabolicHalfModulusNNReal_aut (p : B.parabolic E) :
    parabolicHalfModulusNNReal B (parabolicContinuousAut B σ p) =
      parabolicHalfModulusNNReal B p := by
  change NNReal.sqrt _ = NNReal.sqrt _
  rw [show B.leviProjection E (parabolicContinuousAut B σ p) = leviAut σ B (B.leviProjection E p)
    from leviProjection_entrywiseAut σ B p, leviModulus_leviAut]

/-- Haar measure on the parabolic is invariant under the entrywise action of `σ`. -/
theorem map_parabolicContinuousAut_eq [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] (μP : Measure (B.parabolic E)) [μP.IsHaarMeasure] :
    μP.map (parabolicContinuousAut B σ) = μP := by
  have hcl := B.isClosed_parabolic E
  refine TwistedVanDijk.map_eq_self_of_preimage_eq μP _
    (C := {p : B.parabolic E | (p : GeneralLinear n E) ∈ TwistedVanDijk.integralGL E n})
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (TwistedVanDijk.isCompact_integralGL n))
    ((TwistedVanDijk.isOpen_integralGL n).preimage continuous_subtype_val)
    ⟨1, (TwistedVanDijk.integralGL E n).one_mem⟩ ?_
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, coe_parabolicContinuousAut,
    TwistedVanDijk.entrywiseAut_mem_integralGL_iff]

end LocalField

end Langlands.BaseChange.TwistedLocalDescent
