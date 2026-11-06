import Langlands.Global.Arithmetic.AuxiliaryGeneralPositionReductionProof
import Langlands.Global.Arithmetic.AuxiliaryCharacterFirstOrderProof
import Langlands.Global.Arithmetic.UnitNormWeilStabilizerTransportProof
import Langlands.Global.Arithmetic.GeneralPositionOfExactStabilizerProof

/-! # General position from agreement with an auxiliary character on norm-one units -/

noncomputable section

universe u

namespace Langlands.Global.HarrisDatum

open LocalFactor.CommonClosure GeneralPosition Weil.Local

/-- Agreement on norm-one elements preserves the exact unit-norm stabilizer, when norms and
automorphisms preserve norm one. -/
theorem hasExactUnitNormStabilizer_congr {F : Type*} {M : Type*} [Field F] [NormedField M]
    [Algebra F M] [FiniteDimensional F M] (L : IntermediateField F M) (χ χ' : Lˣ →* ℂˣ)
    (h : ∀ y : Lˣ, ‖((y : L) : M)‖ = 1 → χ y = χ' y)
    (hN : ∀ z : Mˣ, ‖(z : M)‖ = 1 → ‖((Algebra.norm L (z : M) : L) : M)‖ = 1)
    (hσ : ∀ (σ : M ≃ₐ[F] M) (x : M), ‖σ x‖ = ‖x‖)
    (hs : HasExactUnitNormStabilizer L χ) : HasExactUnitNormStabilizer L χ' := by
  intro σ
  rw [← hs σ]
  refine forall_congr' fun z => imp_congr_right fun hz => ?_
  have hz' : ‖((Units.map σ.toRingEquiv.toMonoidHom z : Mˣ) : M)‖ = 1 := by
    rw [Units.coe_map]
    change ‖σ (z : M)‖ = 1
    rw [hσ, hz]
  rw [h _ (by rw [Units.coe_map]; exact hN _ hz'), h _ (by rw [Units.coe_map]; exact hN _ hz)]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

set_option maxHeartbeats 1000000 in
/-- An auxiliary character `χs₀` of `F'ˣ` such that every character agreeing with it on the
norm-one units is in general position, for every normalized reciprocity family. -/
theorem exists_generalPosition_of_unitAgreement (F' : Extension F) :
    ∃ χs₀ : FieldCharacter F F', ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
      ∀ χs : FieldCharacter F F',
        (∀ u : F'.fieldˣ, (F'.asPadicField (p := p)).canonicalNorm (u : F'.field) = 1 →
          χs u = χs₀ u) →
        IsInGeneralPosition F F' (weilCharacter F e F' χs) := by
  let := (fieldData F F').topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let M := galoisClosure F F'
  let h := le_galoisClosure F F'
  let L := IntermediateField.restrict h
  let a := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
  let := (M.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier M.field := IsScalarTower.of_algebraMap_eq' rfl
  let := (M.asPadicField (p := p)).canonicalNormedField
  have : IsGalois F.Carrier M.field := by
    change IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier))
    infer_instance
  obtain ⟨χL, -, -, hstab⟩ := auxiliaryCharacterFirstOrder p F (M.asPadicField (p := p)) L 0
  let c : F'.fieldˣ →ₜ* Lˣ :=
    ⟨a.toMonoidHom, (Langlands.Global.restrictAlgEquiv_continuous F F' M h).units_map _⟩
  refine ⟨χL.comp c, fun e he χs hagree => ?_⟩
  -- Spectral norms are invariant under `F`-automorphisms of `M`.
  have hσ : ∀ (σ : M.field ≃ₐ[F.Carrier] M.field) (x : M.field), ‖σ x‖ = ‖x‖ := by
    intro σ x
    exact (spectralNorm_eq_of_equiv (σ.restrictScalars (Padic p)) x).symm
  -- Norms from `M` to `L` of norm-one elements have norm one.
  have hN : ∀ z : M.fieldˣ, ‖(z : M.field)‖ = 1 →
      ‖((Algebra.norm L (z : M.field) : L) : M.field)‖ = 1 := by
    intro z hz
    change ‖algebraMap L M.field (Algebra.norm L (z : M.field))‖ = 1
    rw [Algebra.norm_eq_prod_automorphisms, norm_prod]
    refine Finset.prod_eq_one fun σ _ => ?_
    change ‖(σ.restrictScalars F.Carrier) (z : M.field)‖ = 1
    rw [hσ, hz]
  have hagreeL : ∀ y : Lˣ, ‖((y : L) : M.field)‖ = 1 →
      χL.toMonoidHom y = (χs.toMonoidHom.comp a.symm.toMonoidHom) y := by
    intro y hy
    have hy' : (F'.asPadicField (p := p)).canonicalNorm ((a.symm y : F'.fieldˣ) : F'.field) = 1 := by
      rw [← Langlands.Global.restrictAlgEquiv_norm F F' M h]
      have hv : (IntermediateField.restrictAlgEquiv h) ((a.symm y : F'.fieldˣ) : F'.field) =
          (y : L) := congrArg (fun z : Lˣ => (z : L)) (a.apply_symm_apply y)
      rw [hv]
      exact hy
    change χL y = χs (a.symm y)
    rw [hagree _ hy']
    change χL y = χL (a (a.symm y))
    rw [a.apply_symm_apply]
  have hunit : HasExactUnitNormStabilizer L (χs.toMonoidHom.comp a.symm.toMonoidHom) :=
    hasExactUnitNormStabilizer_congr L _ _ hagreeL hN hσ hstab
  exact generalPositionOfExactStabilizer p F F' _
    (unitNormWeilStabilizerTransport p F F' e he χs hunit)

end Langlands.Global.HarrisDatum
