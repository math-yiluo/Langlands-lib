import Langlands.Global.Arithmetic.HarrisPairedPlaceRealizationStatement
import Langlands.Global.Arithmetic.CMPairedPlaceModel
import Langlands.Global.Arithmetic.LocalNormalModel

/-! # CM paired-place realization with compatible Harris completion diagrams -/

noncomputable section

universe uF

namespace Langlands.Global

open FieldRealization CMRealization LocalFactor.CommonClosure GeneralPosition

/-- A finite Galois extension of `ℚ_[p]` containing a given finite extension `K`, namely the
normal closure of `K` over `ℚ_[p]` inside an algebraic closure of `K`. -/
theorem exists_galois_extension {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p) :
    ∃ (Ω : Type uF) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra ℚ_[p] Ω)
      (_ : FiniteDimensional ℚ_[p] Ω) (_ : IsGalois ℚ_[p] Ω) (_ : Algebra K.Carrier Ω),
      IsScalarTower ℚ_[p] K.Carrier Ω :=
  ⟨localNormalClosure p K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- Harris's paired-place realization: the CM fields `E ⊆ E' ⊆ L`, the split imaginary
quadratic field `K₀` and the two compatible place data, cut out of the CM rational Galois
model of the normal closure over `ℚ_[p]` of the Galois closure `F̃` of `F' / F`. -/
theorem harrisPairedPlaceRealization : HarrisPairedPlaceRealizationStatement.{uF} := by
  intro p hp F F'
  -- A finite Galois extension `Ω / ℚ_[p]` containing `F̃`.
  obtain ⟨Ω, _, _, _, _, _, aΩ, tΩ⟩ :=
    exists_galois_extension ((galoisClosure F F').asPadicField (p := p))
  -- The `ℚ_[p]`-algebra structures of `F'` and `F̃` underlying their canonical topologies.
  let _ : Algebra ℚ_[p] F'.field := (F'.asPadicField (p := p)).algebra
  let _ : Algebra ℚ_[p] (galoisClosure F F').field :=
    ((galoisClosure F F').asPadicField (p := p)).algebra
  have : IsScalarTower ℚ_[p] F.Carrier F'.field := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- The CM rational Galois model of `Ω`.
  let _ : Algebra (cmModel p Ω) Ω := (cmModelEmbedding p Ω).toRingHom.toAlgebra
  exact pairedPlaceRealization_of_model F F' Ω (aΩ := aΩ) (tΩ := tΩ) (cmModel p Ω)
    (cmModelEmbedding_adjoin p Ω)
    (negSq_neg p) (posSq_pos p Ω) (negSq_isSquare p) (sqrtNeg_sq p Ω) (sqrtPos_sq p Ω)
    (cmModelEmbedding_sqrtNeg p Ω) (cmModelEmbedding_sqrtPos p Ω) (flipPos p Ω)
    (flipPos_central p Ω) (flipPos_sqrtNeg p Ω) (flipPos_sqrtPos p Ω)

end Langlands.Global
