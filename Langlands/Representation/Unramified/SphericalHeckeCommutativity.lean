import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Representation.Hecke.GelfandTrick
import Langlands.Group.GL.Maps
import Langlands.Group.GL.CartanProof

/-! # Commutativity of the actual spherical Hecke algebra of `GL_(r+1)(F)` -/

noncomputable section

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure

universe uF uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

/-- Inverse transpose inverts every diagonal torus element. -/
theorem inverseTranspose_torus {K : Type*} [Field K] {m : ℕ} (ϖ : Kˣ) (lam : Fin m → ℤ) :
    GeneralLinear.inverseTranspose m K (GeneralLinear.Iwasawa.torus ϖ lam) =
      (GeneralLinear.Iwasawa.torus ϖ lam)⁻¹ := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, GeneralLinear.Iwasawa.torus_inv_val,
    Matrix.diagonal_transpose]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The continuous inverse-transpose automorphism of `GL_(r+1)(F)`. -/
abbrev sphericalInverseTranspose (r : ℕ) :
    GeneralLinear (r + 1) F.Carrier ≃ₜ* GeneralLinear (r + 1) F.Carrier :=
  GeneralLinear.inverseTransposeContinuous (r + 1) F.Carrier

/-- Inverse transpose preserves the actual spherical subgroup `GL_(r+1)(O_F)`. -/
theorem inverseTranspose_mem_sphericalSubgroup {r : ℕ} {g : GeneralLinear (r + 1) F.Carrier}
    (hg : g ∈ sphericalSubgroup F r) :
    GeneralLinear.inverseTranspose (r + 1) F.Carrier g ∈ sphericalSubgroup F r := by
  change g ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r at hg
  change _ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r
  rw [Conductor.mem_integralSubgroup] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GeneralLinear.inverseTranspose_entry]
    exact hg.2 j i
  · rw [← map_inv, GeneralLinear.inverseTranspose_entry, inv_inv]
    exact hg.1 j i

theorem preimage_sphericalInverseTranspose (r : ℕ) :
    sphericalInverseTranspose F r ⁻¹'
        (sphericalOpenSubgroup F r : Set (GeneralLinear (r + 1) F.Carrier)) =
      sphericalOpenSubgroup F r := by
  ext g
  constructor
  · intro hg
    have h := inverseTranspose_mem_sphericalSubgroup F (r := r) hg
    rwa [GeneralLinear.inverseTransposeContinuous_apply,
      GeneralLinear.inverseTranspose_involutive] at h
  · intro hg
    exact inverseTranspose_mem_sphericalSubgroup F (r := r) hg

/-- By the Cartan decomposition, inverse transpose sends every element into the
spherical double coset of its inverse. -/
theorem sphericalInverseTranspose_mem_doubleCoset_inv (r : ℕ)
    (x : GeneralLinear (r + 1) F.Carrier) :
    ∃ k₁ k₂ : sphericalOpenSubgroup F r,
      sphericalInverseTranspose F r x = (k₁ : GeneralLinear (r + 1) F.Carrier) * x⁻¹ * k₂ := by
  obtain ⟨ϖ, hϖ⟩ := GeneralLinear.Iwasawa.exists_isUniformizingElement F.Carrier
  obtain ⟨lam, -, k₁, hk₁, k₂, hk₂, hx⟩ := GeneralLinear.Cartan.exists_cartan hϖ (r + 1) x
  have hk₁' : k₁ ∈ sphericalSubgroup F r := hk₁
  have hk₂' : k₂ ∈ sphericalSubgroup F r := hk₂
  refine ⟨⟨GeneralLinear.inverseTranspose (r + 1) F.Carrier k₁ * k₂,
      mul_mem (inverseTranspose_mem_sphericalSubgroup F hk₁') hk₂'⟩,
    ⟨k₁ * GeneralLinear.inverseTranspose (r + 1) F.Carrier k₂,
      mul_mem hk₁' (inverseTranspose_mem_sphericalSubgroup F hk₂')⟩, ?_⟩
  change GeneralLinear.inverseTranspose (r + 1) F.Carrier x = _
  rw [hx, map_mul, map_mul, inverseTranspose_torus]
  group

/-- Inverse transpose preserves the Haar measure of spherical mass one. -/
theorem sphericalHaar_measurePreserving_inverseTranspose (r : ℕ) :
    MeasurePreserving (sphericalInverseTranspose F r) (sphericalHaar F r) (sphericalHaar F r) := by
  have := F.canonicalGeneralLinearLocallyCompactSpace (r + 1)
  have : (sphericalHaar F r).Regular := RankinSelberg.normalizedCompactOpenHaar_regular _ _
  exact Hecke.measurePreserving_of_preimage_eq (sphericalHaar F r) (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) _ (preimage_sphericalInverseTranspose F r)

/-- Gelfand's theorem: the actual spherical Hecke algebra is commutative. -/
theorem sphericalHeckeAlgebra_mul_comm (r : ℕ) (f g : SphericalHeckeAlgebra F r) :
    f * g = g * f :=
  Hecke.HeckeAlgebra.Corner.mul_comm_of_measurePreserving (sphericalHaar F r)
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r)
    (sphericalInverseTranspose F r) (sphericalHaar_measurePreserving_inverseTranspose F r)
    (sphericalInverseTranspose_mem_doubleCoset_inv F r) f g

/-- The standard spherical Hecke operators on an actual fixed space commute. -/
theorem standardHeckeOperator_commute {r : ℕ} (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (i j : Fin (r + 2)) :
    Commute (standardHeckeOperator F A i) (standardHeckeOperator F A j) := by
  unfold standardHeckeOperator
  exact Commute.map (sphericalHeckeAlgebra_mul_comm F r _ _) _

end Langlands.Unramified
