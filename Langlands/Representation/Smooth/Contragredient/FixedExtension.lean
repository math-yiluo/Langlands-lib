import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Smooth.Contragredient.FixedVectorsProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Extension of smooth dual vectors at the same compact open level -/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Compact-open fixed duality bundled as a linear equivalence. -/
def smoothDualCompactFixedEquiv (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    fixedVectors (smoothContragredient ρ) K.toSubgroup ≃ₗ[ℂ]
      Module.Dual ℂ (fixedVectors ρ K.toSubgroup) :=
  LinearEquiv.ofBijective (smoothDualFixedRestriction ρ K.toSubgroup)
    (smoothDualFixedRestriction_bijective ρ hρ K hK)

/-- A chosen linear extension between the fixed smooth duals. It is a right
inverse to pullback whenever the original intertwiner is injective. -/
def smoothDualFixedExtension (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    fixedVectors (smoothContragredient ρ) K.toSubgroup →ₗ[ℂ]
      fixedVectors (smoothContragredient σ) K.toSubgroup :=
  (smoothDualCompactFixedEquiv σ hσ K hK).symm.toLinearMap.comp
    ((fixedVectorsMap f K.toSubgroup).leftInverse.dualMap.comp
      (smoothDualCompactFixedEquiv ρ hρ K hK).toLinearMap)

theorem smoothDualFixedExtension_restrict (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G))
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    smoothDualFixedRestriction σ K.toSubgroup
        (smoothDualFixedExtension hρ hσ f K hK ℓ) =
      (smoothDualFixedRestriction ρ K.toSubgroup ℓ).comp
        (fixedVectorsMap f K.toSubgroup).leftInverse := by
  exact (smoothDualCompactFixedEquiv σ hσ K hK).apply_symm_apply _

theorem smoothDualFixedExtension_pullback (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    fixedVectorsMap (contragredientMap f) K.toSubgroup
      (smoothDualFixedExtension hρ hσ f K hK ℓ) = ℓ := by
  apply (smoothDualFixedRestriction_bijective ρ hρ K hK).1
  have hfK : LinearMap.ker (fixedVectorsMap f K.toSubgroup) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro v w h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  ext v
  change smoothDualFixedRestriction σ K.toSubgroup
    (smoothDualFixedExtension hρ hσ f K hK ℓ) (fixedVectorsMap f K.toSubgroup v) = _
  rw [smoothDualFixedExtension_restrict]
  change smoothDualFixedRestriction ρ K.toSubgroup ℓ
    ((fixedVectorsMap f K.toSubgroup).leftInverse (fixedVectorsMap f K.toSubgroup v)) = _
  rw [LinearMap.leftInverse_apply_of_inj hfK]

/-- Every invariant smooth functional extends without changing the given
compact open subgroup. -/
theorem fixedVectorsMap_contragredient_surjective_of_injective
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Function.Surjective (fixedVectorsMap (contragredientMap f) K.toSubgroup) :=
  fun ℓ => ⟨smoothDualFixedExtension hρ hσ f K hK ℓ,
    smoothDualFixedExtension_pullback hρ hσ f hf K hK ℓ⟩

/-- Evaluation along the original embedding is preserved on every vector. -/
theorem smoothDualFixedExtension_apply (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) (v : V) :
    (smoothDualFixedExtension hρ hσ f K hK ℓ).val.val (f v) = ℓ.val.val v :=
  congrArg (fun a : fixedVectors (smoothContragredient ρ) K.toSubgroup =>
    a.val.val v) (smoothDualFixedExtension_pullback hρ hσ f hf K hK ℓ)

/-- Inverse coefficients agree on the embedded representation. -/
theorem smoothDualFixedExtension_inverseCoefficient
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) (v : V) (g : G) :
    (smoothDualFixedExtension hρ hσ f K hK ℓ).val.val (σ g⁻¹ (f v)) =
      ℓ.val.val (ρ g⁻¹ v) := by
  rw [← f.isIntertwining]
  exact smoothDualFixedExtension_apply hρ hσ f hf K hK ℓ (ρ g⁻¹ v)

end Langlands
