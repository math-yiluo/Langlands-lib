import Langlands.Representation.RankinSelberg.RankOneCharacterReductionStatement
import Langlands.Group.GL.Padic

/-!
# Proof of the reduction of full rank-one Whittaker type to a quasicharacter

The algebraic dual of the carrier is the whole rank-one functional space, hence
linearly equivalent to `ℂ`. A functional corresponding to `1` is then a linear
equivalence of the carrier with `ℂ`, and transporting the action gives a
character. A smooth vector supplies an open kernel, hence continuity.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Topology

universe uF uV uG

section Algebra

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- If the algebraic dual of a complex vector space is linearly equivalent to
`ℂ`, the functional corresponding to `1` is bijective. -/
theorem dual_symm_one_bijective (D : Module.Dual ℂ V ≃ₗ[ℂ] ℂ) :
    Function.Bijective (D.symm 1) := by
  have hφ : ∀ φ : Module.Dual ℂ V, φ = D φ • D.symm 1 := by
    intro φ
    apply D.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  constructor
  · refine (injective_iff_map_eq_zero (D.symm 1)).mpr fun v hv => ?_
    refine (Module.forall_dual_apply_eq_zero_iff ℂ v).mp fun φ => ?_
    rw [hφ φ, LinearMap.smul_apply, hv, smul_zero]
  · obtain ⟨v, hv⟩ : ∃ v : V, D.symm 1 v ≠ 0 := by
      by_contra h
      have h0 : D.symm 1 = 0 := LinearMap.ext fun v => not_not.mp fun hv => h ⟨v, hv⟩
      have h1 := congrArg D h0
      rw [LinearEquiv.apply_symm_apply, map_zero] at h1
      exact one_ne_zero h1
    intro z
    refine ⟨(z / D.symm 1 v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

/-- Every vector is its coordinate times the vector corresponding to `1`. -/
theorem eq_coord_smul_symm_one (L : V ≃ₗ[ℂ] ℂ) (v : V) : v = L v • L.symm 1 := by
  apply L.injective
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

variable {G : Type uG} [Group G]

/-- The scalar by which a group element acts after transport along a linear
equivalence of the carrier with `ℂ`. -/
def transportedScalar (π : Representation ℂ G V) (L : V ≃ₗ[ℂ] ℂ) : G →* ℂ where
  toFun g := L (π g (L.symm 1))
  map_one' := by
    rw [map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    change L (π (g * h) (L.symm 1)) = L (π g (L.symm 1)) * L (π h (L.symm 1))
    have hh := eq_coord_smul_symm_one L (π h (L.symm 1))
    calc L (π (g * h) (L.symm 1)) = L (π g (π h (L.symm 1))) := by
          rw [map_mul, Module.End.mul_apply]
      _ = L (π g (L (π h (L.symm 1)) • L.symm 1)) := by rw [← hh]
      _ = L (π g (L.symm 1)) * L (π h (L.symm 1)) := by
          rw [map_smul, map_smul, smul_eq_mul, mul_comm]

/-- Transport along `L` turns the action into multiplication by the scalar. -/
theorem transportedScalar_apply (π : Representation ℂ G V) (L : V ≃ₗ[ℂ] ℂ)
    (g : G) (v : V) :
    L (π g v) = transportedScalar π L g * L v := by
  have hv := eq_coord_smul_symm_one L v
  calc L (π g v) = L (π g (L v • L.symm 1)) := by rw [← hv]
    _ = transportedScalar π L g * L v := by
      rw [map_smul, map_smul, smul_eq_mul, mul_comm]
      rfl

end Algebra

section RankOne

variable {F : Type uF} [Field F]

/-- In rank one, a matrix is the scalar matrix of its determinant. -/
theorem scalar_determinant_rankOne (g : Langlands.GeneralLinear 1 F) :
    scalar (determinant g) = g := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.GeneralLinearGroup.coe_scalar]

variable [TopologicalSpace F] [IsTopologicalGroup (Langlands.GeneralLinear 1 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A full Whittaker-type representation of GL(1), on an arbitrary complex
module, is equivalent to the scalar representation of a continuous character. -/
theorem exists_quasicharacter_equiv_of_isOfWhittakerType
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (hπ : IsOfWhittakerType 0 (standardCharacter ψ 0) π) :
    ∃ χ : Quasicharacter F,
      Nonempty (π.Equiv (rankOneCharacter (χ : Fˣ →* ℂˣ))) := by
  obtain ⟨⟨hsmooth, -⟩, -, ⟨e⟩⟩ := hπ
  have htop : glFunctionals ψ 0 π = ⊤ := glFunctionals_rankOne ψ π
  let D : Module.Dual ℂ V ≃ₗ[ℂ] ℂ :=
    (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ htop.symm)).trans e
  let L : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective (D.symm 1) (dual_symm_one_bijective D)
  let c : Langlands.GeneralLinear 1 F →* ℂˣ := (transportedScalar π L).toHomUnits
  let χ : Fˣ →* ℂˣ := c.comp scalar
  have hc : Continuous c := by
    obtain ⟨K, hK⟩ := hsmooth (L.symm 1)
    apply continuous_of_continuousAt_one c
    refine (continuousAt_const (y := c 1)).congr ?_
    filter_upwards [K.isOpen.mem_nhds K.one_mem] with k hk
    rw [map_one]
    apply Units.ext
    have hfix : π k (L.symm 1) = L.symm 1 :=
      (Representation.mem_invariants _ _).mp hK ⟨k, hk⟩
    change (1 : ℂ) = L (π k (L.symm 1))
    rw [hfix, LinearEquiv.apply_symm_apply]
  have hχ : Continuous χ := hc.comp (scalarContinuous (R := F) (n := 1)).continuous
  refine ⟨⟨χ, hχ⟩, ⟨Representation.Equiv.mk L fun g => ?_⟩⟩
  apply LinearMap.ext
  intro v
  change L (π g v) = ((χ (determinant g) : ℂˣ) : ℂ) • (1 : Module.End ℂ ℂ) (L v)
  rw [transportedScalar_apply, Module.End.one_apply, smul_eq_mul]
  change _ = ((c (scalar (determinant g)) : ℂˣ) : ℂ) * L v
  rw [scalar_determinant_rankOne]
  rfl

end RankOne

/-- The arbitrary-carrier reduction of full rank-one Whittaker type to the
scalar representation of a continuous quasicharacter. -/
theorem rankOneCharacterReduction : RankOneCharacterReductionStatement.{uF, uV} := by
  intro p _ F ψ V _ _ π hπ
  let := F.canonicalTopologicalData.topology
  have := F.canonicalGeneralLinearTopologicalGroup 1
  exact exists_quasicharacter_equiv_of_isOfWhittakerType ψ π hπ

end Langlands.RankinSelberg
