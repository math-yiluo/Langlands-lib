import Langlands.Representation.Exponents.ScalarGeneralizedEigencharacterProof

/-! # Scalar compatibility of normalized Jacquet modules -/

noncomputable section

namespace Langlands

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem hasScalarCharacter_normalizedJacquet {n : ℕ}
    (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {ω : F.Carrierˣ →* ℂˣ}
    (hω : Classification.HasScalarCharacter ρ GeneralLinear.scalar ω) :
    Classification.HasScalarCharacter (T.normalizedJacquet B ρ)
      (B.scalarLevi F.Carrier) ω := by
  intro a w
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ w
  rw [T.normalizedJacquet_mk,
    show T.leviModulus B (B.scalarLevi F.Carrier a) = 1 from T.leviModulus_scalar B a,
    Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, one_smul, B.leviEmbedding_scalarLevi, hω a v, map_smul]

theorem jacquetExponent_comp_const_eq {n : ℕ}
    (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {ω : F.Carrierˣ →* ℂˣ}
    (hω : Classification.HasScalarCharacter ρ GeneralLinear.scalar ω)
    {χ : (Fin B.length → F.Carrierˣ) →* ℂˣ}
    (hχ : IsGeneralizedEigencharacter (T.splitCentreJacquet B ρ) χ) :
    χ.comp (Pi.constMonoidHom (Fin B.length) F.Carrierˣ) = ω := by
  have hχ' := isGeneralizedEigencharacter_comp (ρ := T.splitCentreJacquet B ρ)
    (Pi.constMonoidHom (Fin B.length) F.Carrierˣ) hχ
  change IsGeneralizedEigencharacter
    ((T.normalizedJacquet B ρ).comp (B.scalarLevi F.Carrier))
    (χ.comp (Pi.constMonoidHom (Fin B.length) F.Carrierˣ)) at hχ'
  exact scalar_generalized_character_eq (ρ := T.normalizedJacquet B ρ)
    (z := B.scalarLevi F.Carrier)
    (T.hasScalarCharacter_normalizedJacquet B hω)
    hχ'

/-- The exact compatibility proposition for the actual normalized quotient. -/
theorem normalizedJacquetScalarCompatibility :
    NormalizedJacquetScalarCompatibility.{uF,uV} T := by
  intro n B V _ _ ρ ω hω
  exact ⟨T.hasScalarCharacter_normalizedJacquet B hω,
    fun χ hχ => T.jacquetExponent_comp_const_eq B hω hχ⟩

end PadicField.TopologicalData

end Langlands
